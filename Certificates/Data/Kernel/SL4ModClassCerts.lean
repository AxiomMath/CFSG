module

public import Certificates.Data.Kernel.SL4ModCerts

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

structure ClassRec where
  L : List Nat
  src : List (Nat × Nat)
  k14 : Nat
  k20 : Nat
  masks : List Nat
  piv : List Nat
  sel : Nat
  B : List Nat
  coef : List Nat
  mB : Nat
  ref : Nat
deriving Inhabited

@[expose] def mkRec (x : List Nat × List (Nat × Nat) × Nat × Nat × List Nat × List Nat × Nat ×
    List Nat × List Nat × Nat × Nat) : ClassRec :=
  { L := x.1, src := x.2.1, k14 := x.2.2.1, k20 := x.2.2.2.1, masks := x.2.2.2.2.1,
    piv := x.2.2.2.2.2.1, sel := x.2.2.2.2.2.2.1, B := x.2.2.2.2.2.2.2.1,
    coef := x.2.2.2.2.2.2.2.2.1, mB := x.2.2.2.2.2.2.2.2.2.1, ref := x.2.2.2.2.2.2.2.2.2.2 }

@[expose] def refsL (refs : Array (Array (Array Nat))) : List (List (List Nat)) :=
  refs.toList.map fun r => r.toList.map Array.toList

@[expose] def echGo (L : List Nat) : List Nat → List Nat → List Nat → Bool
  | prev, mk :: ms, p :: ps =>
    decide (p < 105) && (xorSelL mk L).testBit p &&
      prev.all (fun q => !(xorSelL mk L).testBit q) && echGo L (p :: prev) ms ps
  | _, _, _ => true

@[expose] def echOKL (n : Nat) (L masks piv : List Nat) : Bool :=
  decide (n ≤ masks.length) && decide (n ≤ piv.length) && echGo L [] (masks.take n) (piv.take n)

@[expose] def closedGo (tl : List (List Nat)) (B : List Nat) : List Nat → List Nat → Bool
  | [], _ => true
  | b :: bs, cf =>
    (List.range 6).all (fun s => xorSelL (cf.getD s 0) B == actVL (tl.getD s []) b) &&
      closedGo tl B bs (cf.drop 6)

@[expose] def closedCL (tl : List (List Nat)) (B coef : List Nat) : Bool := closedGo tl B B coef

@[expose] def refOKL (tl : List (List Nat)) (L : List Nat) (rows : List (List Nat)) : Bool :=
  rows.length == 6 && (List.range 6).all fun s =>
    (rows.getD s []).length == L.length && (List.range L.length).all fun k =>
      xorSelL ((rows.getD s []).getD k 0) L == actVL (tl.getD s []) (L.getD k 0)

@[expose] def kindOKL (d : Nat) (refs : List (List (List Nat))) (tl : List (List Nat))
    (c : ClassRec) (k : Nat) : Bool :=
  if k == 0 then decide (d + 1 ≤ c.L.length)
  else if k == 1 then decide (c.B.length < d)
  else if k == 2 then
    decide (c.L.length = d) && decide (c.ref < refs.length) && refOKL tl c.L (refs.getD c.ref [])
  else false

@[expose] def validCL (tl : List (List Nat)) (r14 r20 : List (List (List Nat))) (m : Nat)
    (c : ClassRec) : Bool :=
  derivOKL tl m c.L c.src &&
    (if c.k20 == 0 then echOKL 21 c.L c.masks c.piv
    else if c.k14 == 0 then echOKL 15 c.L c.masks c.piv else true) &&
    (if c.k14 == 1 || c.k20 == 1 then
      nz (xorSelL c.sel c.L) && xorSelL c.mB c.B == xorSelL c.sel c.L && closedCL tl c.B c.coef
    else true) &&
    kindOKL 14 r14 tl c c.k14 && kindOKL 20 r20 tl c c.k20

@[expose] def checkClassFrom (tl : List (List Nat)) (r14 r20 : List (List (List Nat)))
    (od : OrbData) : Nat → List ClassRec → Bool
  | _, [] => true
  | n, c :: cs => validCL tl r14 r20 (expandL od.lab.toList n) c && checkClassFrom tl r14 r20 od (n + 1) cs

end CFSG.LargeExtraspecial.SL4Mod.Native
