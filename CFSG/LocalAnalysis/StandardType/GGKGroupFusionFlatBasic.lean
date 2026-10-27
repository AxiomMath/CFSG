module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlat
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionTop

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGKGroupFusionAtFlat.of_cover {S S₁ S₂ : TauCeti.CFSGIndex → ℕ → Prop}
    (hcov : ∀ i p, p.Prime → p ≠ 2 → S i p → S₁ i p ∨ S₂ i p) (h₁ : GGKGroupFusionAtFlat S₁)
    (h₂ : GGKGroupFusionAtFlat S₂) : GGKGroupFusionAtFlat S := by
  intro W _ _ p H E i hi hyp hL hK he
  rcases hcov i p hyp.1.1 hyp.1.2.1 hi with h | h
  · exact h₁ W p H E i h hyp hL hK he
  · exact h₂ W p H E i h hyp hL hK he

theorem ggKGroupFusionAtFlat_cyclic : GGKGroupFusionAtFlat GGKFCyclic := by
  rintro W _ _ p H E i ⟨q, hq, rfl⟩ hyp - - ⟨e⟩
  exfalso
  obtain ⟨a, b, hab⟩ := hyp.2.1.2.1
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm _ _

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggHypThreeSixteenFlat_eq_top_of_le (hSch : SchreierFor InCatalog) {W : Type} [Group W]
    [Finite W] {p : ℕ} {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E)
    (hKH : CFSG.generalizedFitting W ≤ H) : H = ⊤ := by
  obtain ⟨⟨hp, -, hE, hEcard, hfus⟩, ⟨hsimple, hnab, hcat⟩, -⟩ := hyp
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hsimple
  have hout := hSch _ hnab hcat
  exact hfus.eq_top_of_le_of_isSolvable hp hE hEcard hKH
    (ggIsSolvable_quot_generalizedFitting hsimple hnab hout)

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggKGroupFusionLayerInputFlat_of_atK (hSch : SchreierFor InCatalog)
    (h : GGKGroupFusionAtFlatK fun _ _ => True) : GGKGroupFusionLayerInputFlat := by
  intro W _ _ hW p H E hyp hL
  by_cases hKH : CFSG.generalizedFitting W ≤ H
  · exact Or.inl (ggHypThreeSixteenFlat_eq_top_of_le hSch hyp hKH)
  · obtain ⟨i, he⟩ := hyp.2.1.2.2
    exact Or.inr (h W hW p H E i trivial hyp hL hKH he)

theorem ggKGroupFusionAtFlatK_of_families (hA : GGKGroupFusionAtFlat GGKFAlternating)
    (hD : GGKGroupFusionAtFlat GGKFLieDefining) (hC : GGKGroupFusionAtFlat GGKFLieCross)
    (hS : GGKGroupFusionAtFlatK GGKFSporadic) : GGKGroupFusionAtFlatK fun _ _ => True := by
  intro W _ _ hW p H E i _ hyp hL hK he
  rcases ggKF_cases i p with h | h | h | h | h
  · exact ggKGroupFusionAtFlat_cyclic W p H E i h hyp hL hK he
  · exact hA W p H E i h hyp hL hK he
  · exact hD W p H E i h hyp hL hK he
  · exact hC W p H E i h hyp hL hK he
  · exact hS W hW p H E i h hyp hL hK he

section Hyp

variable {W : Type} [Group W]

theorem ggIsSolvable_quot_inf_generalizedFitting_flat [Finite W]
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) {p : ℕ}
    {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat p H E) :
    have : (CFSG.generalizedFitting W).Normal :=
      CFSG.LocalCores.generalized_fitting_characteristic.2
    Group.IsSolvable
      (↥H ⧸ ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker) := by
  intro hKn
  obtain ⟨-, ⟨hsimple, hnab, hcat⟩, -⟩ := hyp
  have : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hsimple
  have hout := hSch _ hnab hcat
  have hWK := ggIsSolvable_quot_generalizedFitting hsimple hnab hout
  exact Group.isSolvable_of_isSolvable_injective
    (QuotientGroup.kerLift_injective
      ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype))

end Hyp

end CFSG.StandardType
