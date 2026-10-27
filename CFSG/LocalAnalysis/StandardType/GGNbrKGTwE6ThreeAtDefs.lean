module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint
open scoped commutatorElement

@[expose] def GGTwoLocalAt (p r s : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  Finite R → ∀ a : MulAut R, a ^ p = 1 → a ∈ Subgroup.closure (I ∪ F) →
    a ∉ (MulAut.conj : R →* MulAut R).range →
    ∃ E : Subgroup (MulAut R),
      E ≤ Subgroup.zpowers a ⊔ (MulAut.conj : R →* MulAut R).range ∧
      IsElemAbelian p E ∧ GGTwoLocalAut E ∧ p ^ r ≤ Nat.card E ∧
      (a ∉ I → p ^ s ≤ Nat.card E)

@[expose] def GGNbrKGTwE6ThreeAddTwoLocalAt : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTwoLocalAt 3 5 6 R I F

end CFSG.StandardType
