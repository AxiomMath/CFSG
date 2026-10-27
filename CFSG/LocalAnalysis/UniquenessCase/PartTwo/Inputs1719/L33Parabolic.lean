module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def IsL33ParabolicRadical {Y : Type} [Group Y] [Finite Y]
    (K S U : Subgroup Y) : Prop :=
  U ≤ K ∧ IsElemAbelian 3 U ∧ Nat.card U = 9 ∧
    S ⊓ K ≤ Subgroup.normalizer (U : Set Y) ∧
    ∀ E : Subgroup Y, E ≤ U → Permutes E (S ⊓ K) → E = ⊥ ∨ E = U

@[expose] def K_L33ParabolicPair : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    LieModel ↥K .PSL 3 3 1 →
    (∀ x ∈ S, ∀ y ∈ S, x ∉ K → y ∉ K → x * y ∈ K) ∧
    ∃ U₁ U₂ : Subgroup Y, IsL33ParabolicRadical K S U₁ ∧
      IsL33ParabolicRadical K S U₂ ∧ U₁ ⊔ U₂ = K

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
