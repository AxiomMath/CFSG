module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.RankThree.Asc83Table.Native

open CFSG.SectionRank.Native

abbrev Word := List (Nat × Nat)

inductive MFact where
  | ord (r e : Nat)
  | conj (h : Nat) (u w : Word)
  | ne (w₁ w₂ : Word) (t : Nat)
  | eq (w₁ w₂ : Word)
deriving Inhabited, DecidableEq

structure MCert where
  nregs : Nat
  prog : List Op
  facts : List MFact

variable {M V : Type} (O : Ops M V)

@[expose] def evalW [Inhabited M] (R : Array M) : Word → M
  | [] => O.one
  | (r, e) :: w => O.mul (O.pow R[r]! e) (evalW R w)

@[expose] def wordLt (n : Nat) (w : Word) : Bool := w.all fun p => decide (p.1 < n)

@[expose] def factOK [Inhabited M] (R : Array M) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && O.eq (O.pow R[r]! e) O.one
  | .conj h u w => decide (h < n) && wordLt n u && wordLt n w &&
      O.eq (O.mul R[h]! (evalW O R u)) (O.mul (evalW O R w) R[h]!)
  | .ne w₁ w₂ t => wordLt n w₁ && wordLt n w₂ &&
      O.vne (O.vmul (O.unit t) (evalW O R w₁)) (O.vmul (O.unit t) (evalW O R w₂))
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && O.eq (evalW O R w₁) (evalW O R w₂)

@[expose] def mcertCheck [Inhabited M] (seedA seedB : String) (C : MCert) : Bool :=
  let R := O.regsOf seedA seedB C.nregs C.prog
  decide (2 ≤ C.nregs) && C.prog.all (Op.lt C.nregs) && C.facts.all (factOK O R C.nregs)

end CFSG.RankThree.Asc83Table.Native
