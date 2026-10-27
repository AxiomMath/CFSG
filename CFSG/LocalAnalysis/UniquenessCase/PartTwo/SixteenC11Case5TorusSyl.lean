module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

theorem s16c11_case5_card_N1 (hK : Nat.card K = 4) :
    Nat.card ↥(s16c11_case5_N1 (K := K)) = 21600 := by
  haveI := s16c11_case5_charP hK
  have h4 : 4 ≤ Nat.card K := by rw [hK]
  have hle : s16c11_case5_N1 (K := K) ≤
      s16c11_case5_lrRange ⊔ Subgroup.zpowers (s16c11_case5_sigma (K := K)) :=
    s16c11_case5_N1_le (K := K) h4
  have hge : s16c11_case5_lrRange ⊔ Subgroup.zpowers (s16c11_case5_sigma (K := K)) ≤
      s16c11_case5_N1 (K := K) := by
    unfold s16c11_case5_N1
    refine sup_le (le_inf s16c11_case5_lrRange_le_normalizer
      s16c11_case5_lrRange_le_centralizer) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_inf]
    exact ⟨s16c11_case5_trM_mem_normalizer, s16c11_case5_trM_mem_centralizer_scal⟩
  have heq : s16c11_case5_N1 (K := K) =
      s16c11_case5_lrRange ⊔ Subgroup.zpowers (s16c11_case5_sigma (K := K)) :=
    le_antisymm hle hge
  rw [heq]
  have haN : ∀ t ∈ s16c11_case5_lrRange (K := K),
      s16c11_case5_sigma * t * s16c11_case5_sigma⁻¹ ∈ s16c11_case5_lrRange := by
    intro t ht
    rw [s16c11_case5_mem_lrRange] at ht ⊢
    obtain ⟨A, B, rfl⟩ := ht
    refine ⟨B, A, ?_⟩
    rw [inv_eq_of_mul_eq_one_right (trM_mul_self (K := K)), s16c11_case5_trM_conj_lr]
  have ha2 : s16c11_case5_sigma (K := K) ^ 2 = 1 := by
    rw [pow_two, trM_mul_self (K := K)]
  rw [CFSG.GH74.GLS.C3.Layer2.card_sup_zpowers haN ha2
    s16c11_case5_trM_not_mem_lrRange, s16c11_case5_card_lrRange hK]

theorem s16c11_case5_card_S0 (hK : Nat.card K = 4) :
    Nat.card ↥(s16c11_case5_S0 (K := K)) = 32 := by
  have hRange : (rho (K := K)).range ≤ s16c11_case5_lrRange (K := K) := by
    rintro x ⟨⟨g, h⟩, rfl⟩
    exact s16c11_case5_mem_lrRange.mpr ⟨Matrix.SpecialLinearGroup.toGL g,
      Matrix.SpecialLinearGroup.toGL h, rfl⟩
  have hVlr : s16c11_case5_V (K := K) ≤ s16c11_case5_lrRange (K := K) :=
    s16c11_case5_V_le_range.trans hRange
  have haT : s16c11_case5_sigma ∉ s16c11_case5_V (K := K) :=
    fun h => s16c11_case5_trM_not_mem_lrRange (hVlr h)
  have haN : ∀ t ∈ s16c11_case5_V (K := K),
      s16c11_case5_sigma * t * s16c11_case5_sigma⁻¹ ∈ s16c11_case5_V := by
    intro t ht
    rw [s16c11_case5_mem_V] at ht ⊢
    obtain ⟨⟨a, b⟩, rfl⟩ := ht
    refine ⟨(b, a), ?_⟩
    rw [inv_eq_of_mul_eq_one_right (trM_mul_self (K := K)),
      s16c11_case5_sigma_conj_rhoU]
  have ha2 : s16c11_case5_sigma (K := K) ^ 2 = 1 := by
    rw [pow_two, trM_mul_self (K := K)]
  unfold s16c11_case5_S0
  rw [CFSG.GH74.GLS.C3.Layer2.card_sup_zpowers haN ha2 haT, s16c11_case5_card_V hK]

theorem s16c11_case5_isSylowIn_S0 (hK : Nat.card K = 4) :
    IsSylowIn 2 (s16c11_case5_S0 (K := K)) (s16c11_case5_N1 (K := K)) := by
  haveI : CharP K 2 := s16c11_case5_charP hK
  have hle := s16c11_case5_S0_le_N1 (K := K)
  have h0 := s16c11_case5_card_S0 (K := K) hK
  have h1 := s16c11_case5_card_N1 (K := K) hK
  refine ⟨hle, IsPGroup.of_card (n := 5) (by rw [h0]; norm_num), ?_⟩
  have h := Subgroup.relIndex_mul_card (H := s16c11_case5_S0 (K := K))
    (K := s16c11_case5_N1 (K := K))
  rw [inf_eq_left.mpr hle, h0, h1] at h
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
