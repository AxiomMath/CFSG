module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14OuterAut
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14OuterQ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.HardMathSupport.U4FF (disp disp_conj)

theorem finU4_outer_disp_ge
    {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)]
    {L : Subgroup (MulAut S)} (hL : IsU4Group 1 L) (hirr : IsIrrOn L)
    (hS : Nat.card S = 2 ^ 14) {σ : MulAut S}
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut S))) (hσ2 : σ * σ = 1) (hσL : σ ∉ L) :
    4 ≤ disp σ := by
  obtain ⟨K, _, _, _, hK, η, Z, τ, hτ, hZ, hrel⟩ :=
    finU4_outer_normal_form hL hirr hσN hσ2 hσL
  obtain ⟨E, _, _, _, _, hE⟩ := finU4_fourteen_normalizer_matrix hL hirr hS hK η
  have hσ'N : τ * σ * τ⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut S)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hτ) hσN)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hτ))
  have hσ'2 : (τ * σ * τ⁻¹) * (τ * σ * τ⁻¹) = 1 := by
    have h : (τ * σ * τ⁻¹) * (τ * σ * τ⁻¹) = τ * (σ * σ) * τ⁻¹ := by group
    rw [h, hσ2]
    group
  obtain ⟨N, hN1, hN2, hdisp⟩ := hE Z (τ * σ * τ⁻¹) hσ'N hrel
  have h4 := finU4_intertwiner_rank hK hZ N hN1 (hN2 hσ'2)
  rw [← disp_conj τ σ, hdisp]
  exact h4

end CFSG.LocalAnalysis.WeakClosure81
