module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.KC.ThThreeCov

open CFSG.SectionRank.Native

@[expose] def opLetters (ψ : Nat → Nat) : Op → List Nat
  | .mul i j _ => [ψ i, ψ j]
  | .pow e i _ => List.replicate e (ψ i)

@[expose] def opOut : Op → Nat
  | .mul _ _ k => k
  | .pow _ _ k => k

@[expose] def updMap (ψ : Nat → Nat) (k f : Nat) : Nat → Nat := fun r => if r = k then f else ψ r

@[expose] def simOK (D : List (List Nat)) : (Nat → Nat) → Nat → List Op → Bool
  | _, _, [] => true
  | ψ, f, o :: p => decide (5 ≤ f) && decide (f - 5 < D.length) &&
      D.getD (f - 5) [] == opLetters ψ o && simOK D (updMap ψ (opOut o) f) (f + 1) p

@[expose] def simMap : (Nat → Nat) → Nat → List Op → Nat → Nat
  | ψ, _, [] => ψ
  | ψ, f, o :: p => simMap (updMap ψ (opOut o) f) (f + 1) p

@[expose] def psi0 : Nat → Nat := fun r => if r = 0 then 0 else if r = 1 then 1 else 5

@[expose] def abL (l : Int) : Nat := if l = 1 then 0 else 1

end CFSG.KC.ThThreeCov

end
