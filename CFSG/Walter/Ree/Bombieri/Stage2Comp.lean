module

public import CFSG.Walter.Ree.Bombieri.SpecComp
public import CFSG.Walter.Ree.Bombieri.Subst

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P

section

variable (T : Tab)

@[expose] def frobT (a : F3P) : ℕ → F3P
  | 0 => a
  | e + 1 =>
    let b := frobT a e
    mulT T b (mulT T b b)

@[expose] def substPt (k lam : ℕ) (neg : Bool) (ws : List F3P) (j : ℕ) : F3P :=
  frobT T (normalize (ws.getD (substIdx k neg j) zero)) (substExp k lam neg j)

@[expose] def qVal (c : ℕ → F3P) (ε : ℤ) : F3P :=
  (Elim.qExpr ε).evalM (mulT T) c fun _ => zero

@[expose] def check2 (k lam : ℕ) (neg : Bool) (ws : List F3P) : Bool :=
  let c := substPt T k lam neg ws
  unitT T (qVal T c 0) && unitT T (qVal T c 1) && unitT T (qVal T c (-1)) &&
    specCheck T (c 0) (c 1) (c 2) (c 3) (c 4)

end

structure Entry where
  k : ℕ
  lam : ℕ
  neg : Bool
  ws : List ℕ

@[expose] def Entry.key (e : Entry) : ℕ × ℕ × Bool := (e.k, e.lam, e.neg)

@[expose] def batchCheck (T : Tab) (es : List Entry) : Bool :=
  es.all fun e => check2 T e.k e.lam e.neg (e.ws.map ofCode)

@[expose] def fieldBatchCheck (f : F3P) (m : ℕ) (g : F3P) (es : List Entry) : Bool :=
  let T := mkTab f m g
  rootCheck f m && tabCheck T && batchCheck T es

end Spec

end CFSG.Walter.Ree.Bombieri
