module

public meta import Lean

open Lean Elab Term

namespace CFSG.Sporadic.Schreier.NatListLit

meta def listTy : Nat → Expr
  | 0 => mkConst ``Nat
  | d + 1 => mkApp (mkConst ``List [0]) (listTy d)

meta partial def depth (s : Syntax) : Except String Nat :=
  match s.isNatLit? with
  | some _ => pure 0
  | none =>
    if s.getKind == ``«term[_]» then
      match s[1].getSepArgs[0]? with
      | some e => return (← depth e) + 1
      | none => throw "natLit%: empty list"
    else throw "natLit%: expected a numeral or a list literal"

meta partial def build (s : Syntax) : Nat → Except String Expr
  | 0 => match s.isNatLit? with
    | some n => pure (mkNatLit n)
    | none => throw "natLit%: expected a numeral"
  | d + 1 => do
    unless s.getKind == ``«term[_]» do throw "natLit%: expected a list literal"
    let ty := listTy d
    let es := s[1].getSepArgs
    let mut acc := mkApp (mkConst ``List.nil [0]) ty
    for i in [0:es.size] do
      acc := mkApp3 (mkConst ``List.cons [0]) ty (← build es[es.size - 1 - i]! d) acc
    return acc

end CFSG.Sporadic.Schreier.NatListLit

open CFSG.Sporadic.Schreier.NatListLit in
elab "natLit% " t:term : term => do
  match depth t >>= build t with
  | .ok e => return e
  | .error m => throwErrorAt t m
