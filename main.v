module main

type Expr =
	EInt      |
	EVar      |
	EFunc     |
	EFuncCall |
	EIf

struct EInt {
pub:
	value i64
}

struct EVar {
pub:
	name  string
}

struct EFunc {
pub:
	param string
	body  Expr
}

struct EFuncCall {
pub:
	func  Expr
	arg   Expr
}

struct EIf {
pub:
	cond  Expr
	true_ Expr
	fals_ Expr
}

type Type =
	TNamed  |
	TVar    |
	TFunc

struct TNamed {
pub:
	name  string
}

struct TVar {
pub:
	name  string
}

struct TFunc {
pub:
	from  Type
	to    Type
}

struct Context {
mut:
	next  i64
	env   map[string]Type
	subst map[string]Type
}

fn (ctx Context) clone() Context {
	return Context {
		next: ctx.next,
		env: ctx.env.clone(),
		subst: ctx.subst.clone(),
	}
}

fn main() {
	mut ctx := Context{
		env: {
			'true': TNamed { name: "Bool" },
			'false': TNamed { name: "Bool" },
			'f': TFunc {
				from: TNamed {
					name: 'Int'
				},

				to: TNamed {
					name: 'Int'
				}
			}
			'+': TFunc { from: TNamed { name: "Int" }, to: TNamed { name: "Int" } }
		}
	}

	mut node := Expr(EFunc {
		param: 'x',
		body: EFuncCall {
			func: EVar {
				name: 'f'
			},
			arg: EVar {
				name: 'x'
			}
		}
	})

	mut inferred, _ := infer(mut ctx, node)

	node = Expr(EFuncCall {
		func: EVar {
			name: 'f'
		},
		arg: EInt {
			value: 1
		}
	})

	inferred, _ = infer(mut ctx, node)
	println('inferred ${inferred}')

	node = EFuncCall {
		func: EVar {
			name: "+"
		},
		arg: EVar {
			name: 'true'
		}
	}

	inferred, _ = infer(mut ctx, node)
	println('inferred ${inferred}')
}

fn infer(mut ctx Context, e Expr) (Type, map[string]Type) {
	match e {
		EInt {
			return TNamed {
				name: 'Int'
			}, map[string]Type{}
		}

		EVar {
			type_ := ctx.env[e.name] or {
				panic('Unbound var ${e.name}')
			}

			return type_, map[string]Type{}
		}

		EFunc {
			new_type := new_t_var(mut ctx)
			mut new_ctx  := add_to_context(mut ctx, e.param, new_type)
			body_type, subst := infer(mut new_ctx, e.body)
			inferred_type := TFunc {
				from: apply_subst_to_type(subst, new_type),
				to: body_type
			}
			return inferred_type, subst
		}

		EFuncCall {
			func_type, s1 := infer(mut ctx, e.func)
			mut ctx_ := apply_subst_to_ctx(s1, mut ctx)
			arg_type, s2 := infer(mut ctx_, e.arg)
			new_var := new_t_var(mut ctx)
			s3 := compose_subst(s1, s2)
			s4 := unify(TFunc { from: arg_type, to: new_var }, func_type)
			func_type_1 := apply_subst_to_type(s4, func_type)
			s5 := compose_subst(s3, s4)
			s6 := unify(apply_subst_to_type(s5, (func_type_1 as TFunc).from), arg_type)
			result_subst := compose_subst(s5, s6)
			return apply_subst_to_type(result_subst, (func_type_1 as TFunc).to), result_subst
		}

		EIf {
			cond_type, s0 := infer(mut ctx, e.cond)
			s1 := unify(cond_type, TNamed { name: "Bool" })
			mut ctx1 := apply_subst_to_ctx(compose_subst(s0, s1), mut ctx)
			true_branch_type_, s2  := infer(mut ctx1, e.true_)
			s3 := compose_subst(s1, s2)
			mut ctx2 := apply_subst_to_ctx(s2, mut ctx1)
			false_branch_type_, s4 := infer(mut ctx2, e.fals_)
			s5 := compose_subst(s3, s4)
			true_branch_type := apply_subst_to_type(s5, true_branch_type_)
			false_branch_type := apply_subst_to_type(s5, false_branch_type_)
			s6 := unify(true_branch_type, false_branch_type)
			result_subst := compose_subst(s5, s6)

			return apply_subst_to_type(s6, true_branch_type), result_subst
		}
	}
}

fn new_t_var(mut ctx Context) Type {
	new_var_num := ctx.next
	ctx.next++
	return TVar {
		name: 'T${new_var_num}'
	}
}

fn add_to_context(mut ctx Context, name string, t Type) Context {
	mut new_ctx := Context {
		env: ctx.env.clone(),
		subst: ctx.subst.clone(),
	}

	new_ctx.env[name] = t

	return new_ctx
}

fn apply_subst_to_ctx(subst map[string]Type, mut ctx Context) Context {
	mut new_ctx := ctx.clone()

	for k, v in new_ctx.env {
		t := v
		new_ctx.env[k] = apply_subst_to_type(subst, t)
	}

	return new_ctx
}

fn apply_subst_to_type(subst map[string]Type, t Type) Type {
	match t {
		TNamed {
			return t
		}

		TVar {
			subst_ := subst[t.name] or {
				return t
			}

			return subst_
		}

		TFunc {
			return TFunc {
				from: apply_subst_to_type(subst, t.from),
				to: apply_subst_to_type(subst, t.to),
			}
		}
	}
}

fn unify(t1 Type, t2 Type) map[string]Type {
	if t1 is TNamed && t2 is TNamed && (t1 as TNamed).name == (t2 as TNamed).name {
		return {}
	} else if t1 is TVar {
		return var_bind(t1.name, t2)
	} else if t2 is TVar {
		return var_bind(t2.name, t1)
	} else if t1 is TFunc && t2 is TFunc {
		s1 := unify(t1.from, t2.from)
		s2 := unify(
			apply_subst_to_type(s1, t1.to),
			apply_subst_to_type(s1, t2.to)
		)

		return compose_subst(s1, s2)
	} else {
		panic('Type mismatch:\nExpecting ${t1}\nFound ${t2}')
	}
}

fn var_bind(name string, t Type) map[string]Type {
	if t is TVar && (t as TVar).name == name {
		return map[string]Type{}
	} else if contains(t, name) {
		panic('Type ${t} contains a reference to itself')
	} else {
		mut subst := map[string]Type{}
		subst[name] = t
		return subst
	}
}

fn contains(t Type, name string) bool {
	match t {
		TNamed {
			return false
		}

		TVar {
			return t.name == name
		}

		TFunc {
			return contains(t.from, name) || contains(t.to, name)
		}
	}
}

fn compose_subst(s1 map[string]Type, s2 map[string]Type) map[string]Type {
	mut s2_ := map[string]Type

	for k, v in s2 {
		s2_[k] = apply_subst_to_type(s1, v)
	}

	mut s1_ := s1.clone()

	for k, v in s2_ {
		s1_[k] = v
	}

	return s1_
}