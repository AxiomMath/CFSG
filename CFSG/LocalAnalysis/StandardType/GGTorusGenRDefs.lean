module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusGenR (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∀ x ∈ E, x ≠ 1 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
      ∀ c ∈ Subgroup.centralizer (E : Set R), (∃ k : ℕ, c ^ p ^ k = 1) →
        ∃ (S : Subgroup R) (W : Set R), IsPGroup p S ∧ S ≤ Subgroup.centralizer (E : Set R) ∧
          S ≤ J ∧ W ⊆ Subgroup.normalizer (E : Set R) ∧
          c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set R))

end CFSG.StandardType
