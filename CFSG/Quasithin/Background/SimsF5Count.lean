module

public import CFSG.Quasithin.Background.SimsF5Inv

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix

local notation:max "mat(" g ")" => ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))

theorem cnt_isIdempotent {w : GL6} (hww : w * w = 1) :
    IsIdempotentElem (Matrix.mulVecLin (mat(w) - 1)) := by
  refine LinearMap.ext fun v => ?_
  change (mat(w) - 1) *ᵥ ((mat(w) - 1) *ᵥ v) = (mat(w) - 1) *ᵥ v
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, inv_mulVec_mulVec hww]
  funext i
  simp only [Pi.sub_apply]
  exact (by decide : ∀ a b : ZMod 3, a - b - (b - a) = b - a) _ _

theorem cnt_trace_eq_finrank {w : GL6} (hww : w * w = 1) :
    Matrix.trace mat(w) = (Module.finrank (ZMod 3) (commSp w) : ZMod 3) := by
  have h1 := (LinearMap.IsIdempotentElem.isProj_range _ (cnt_isIdempotent hww)).trace
  have h2 : LinearMap.trace (ZMod 3) (Fin 6 → ZMod 3) (Matrix.mulVecLin (mat(w) - 1)) =
      Matrix.trace (mat(w) - 1) := Matrix.trace_toLin'_eq _
  rw [h2] at h1
  rw [Matrix.trace_sub, Matrix.trace_one] at h1
  have h6 : ((Fintype.card (Fin 6) : ℕ) : ZMod 3) = 0 := by decide
  rw [h6, sub_zero] at h1
  exact h1

theorem cnt_conj_z_iff {w : GL6} (hw : w ∈ MDot) (hww : w * w = 1) :
    (∃ g ∈ MDot, g * zDot * g⁻¹ = w) ↔ Matrix.trace mat(w) = 1 := by
  rw [cnt_trace_eq_finrank hww]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [(inv_z_conj hg).1]
    decide
  · intro h
    by_cases hw1 : w = 1
    · subst hw1
      rw [commSp, Units.val_one, sub_self, Matrix.mulVecLin_zero, LinearMap.range_zero,
        finrank_bot] at h
      exact absurd h (by decide)
    · rcases inv_dim hw hw1 hww with h2 | h4
      · rw [h2] at h
        exact absurd h (by decide)
      · exact inv_exists_z hw hww h4

theorem cnt_ncard_inter {H : Subgroup GL6} (hM : H ≤ MDot) (hsq : ∀ y ∈ H, y * y = 1)
    {L : Finset GL6} (hL : (H : Set GL6) = ↑L) :
    ({y : GL6 | ∃ g ∈ MDot, g * zDot * g⁻¹ = y} ∩ (H : Set GL6)).ncard =
      (L.filter fun y => Matrix.trace mat(y) = 1).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hL, Finset.mem_coe, Finset.coe_filter]
  constructor
  · rintro ⟨hc, hy⟩
    have hyH : y ∈ H := by rw [← SetLike.mem_coe, hL]; exact hy
    exact ⟨hy, (cnt_conj_z_iff (hM hyH) (hsq y hyH)).1 hc⟩
  · rintro ⟨hy, ht⟩
    have hyH : y ∈ H := by rw [← SetLike.mem_coe, hL]; exact hy
    exact ⟨(cnt_conj_z_iff (hM hyH) (hsq y hyH)).2 ht, hy⟩

theorem cnt_sq_of_isEn {n : ℕ} {H : Subgroup GL6} (h : IsEn n ↥H) : ∀ y ∈ H, y * y = 1 :=
  fun y hy => congrArg Subtype.val (h.2.1 ⟨y, hy⟩)

theorem cnt_ADot_le_MDot {Mi : Subgroup GL6} (h : Mi ≤ MDot) : ADot Mi ≤ MDot :=
  (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_left.trans h)

theorem cnt_M1Dot_le_MDot : M1Dot ≤ MDot := inf_le_left

@[expose] def cntEvenSets : Finset (Finset (Fin 6)) := Iset.powerset.filter fun J => Even J.card

theorem cnt_Q2Dot_eq : (Q2Dot : Set GL6) = ↑(cntEvenSets.image eJ) := by
  rw [Q2Dot_coe]
  ext g
  simp only [cntEvenSets, Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter,
    Finset.mem_powerset, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨J, hJ, hev, rfl⟩
    exact ⟨J, ⟨hJ, hev⟩, rfl⟩
  · rintro ⟨J, ⟨hJ, hev⟩, rfl⟩
    exact ⟨J, hJ, hev, rfl⟩

theorem ncard_zCls_Q2Dot :
    ({y : GL6 | ∃ g ∈ MDot, g * zDot * g⁻¹ = y} ∩ (Q2Dot : Set GL6)).ncard = 5 := by
  rw [cnt_ncard_inter mono_Q2Dot_le_MDot (cnt_sq_of_isEn isEn_Q2Dot) cnt_Q2Dot_eq]
  decide +kernel

@[expose] def cntA1 : Finset GL6 :=
  Finset.univ.image aiE ∪ Finset.univ.image fun k => fDot * aiE k

theorem cnt_card_A1 : cntA1.card = 16 := by decide +kernel

theorem cnt_ADot_M1Dot_coe : (ADot M1Dot : Set GL6) = ↑cntA1 := by
  have hcard : Nat.card ↥(ADot M1Dot) = 16 := by
    rw [ADot_M1Dot_eq]
    exact (ai_R_card ai_card_CQ1 ai_fDot_not_mem_Q1Dot).2
  have hncard : (ADot M1Dot : Set GL6).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro y hy
    simp only [cntA1, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range] at hy
    rw [SetLike.mem_coe, ADot_M1Dot_eq]
    rcases hy with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact Subgroup.mem_sup_right (ai_mem_CQ1_iff.2 ⟨k, rfl⟩)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (ai_mem_CQ1_iff.2 ⟨k, rfl⟩))
  · rw [Set.ncard_coe_finset, cnt_card_A1, hncard]
  · exact Set.finite_of_ncard_ne_zero (by rw [hncard]; decide)

theorem ncard_zCls_ADot_M1Dot :
    ({y : GL6 | ∃ g ∈ MDot, g * zDot * g⁻¹ = y} ∩ (ADot M1Dot : Set GL6)).ncard = 5 := by
  rw [cnt_ncard_inter (cnt_ADot_le_MDot cnt_M1Dot_le_MDot) (cnt_sq_of_isEn ADot_M1Dot_isEn)
    cnt_ADot_M1Dot_coe]
  decide +kernel

@[expose] def cntSymSets : Finset (Finset (Fin 6)) :=
  Iset.powerset.filter fun J => Even J.card ∧ ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J)

@[expose] def cntA2 : Finset GL6 :=
  cntSymSets.image eJ ∪ cntSymSets.image fun J => fDot * eJ J

theorem cnt_card_A2 : cntA2.card = 16 := by decide +kernel

theorem cnt_eJ_mem_CQ2 {J : Finset (Fin 6)} (hJ : J ∈ cntSymSets) :
    eJ J ∈ Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) := by
  simp only [cntSymSets, Finset.mem_filter, Finset.mem_powerset] at hJ
  have : eJ J ∈ ((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) : Set GL6) := by
    rw [Q2Dot_inf_centralizer_coe]
    exact ⟨J, hJ.1, hJ.2.1, hJ.2.2, rfl⟩
  exact this

theorem cnt_ADot_M2Dot_coe : (ADot M2Dot : Set GL6) = ↑cntA2 := by
  have hcard : Nat.card ↥(ADot M2Dot) = 16 := by
    rw [ADot_M2Dot_eq]
    exact (ai_R_card ai_card_CQ2 ai_fDot_not_mem_Q2Dot).2
  have hncard : (ADot M2Dot : Set GL6).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro y hy
    simp only [cntA2, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hy
    rw [SetLike.mem_coe, ADot_M2Dot_eq]
    rcases hy with ⟨J, hJ, rfl⟩ | ⟨J, hJ, rfl⟩
    · exact Subgroup.mem_sup_right (cnt_eJ_mem_CQ2 hJ)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (cnt_eJ_mem_CQ2 hJ))
  · rw [Set.ncard_coe_finset, cnt_card_A2, hncard]
  · exact Set.finite_of_ncard_ne_zero (by rw [hncard]; decide)

theorem ncard_zCls_ADot_M2Dot :
    ({y : GL6 | ∃ g ∈ MDot, g * zDot * g⁻¹ = y} ∩ (ADot M2Dot : Set GL6)).ncard = 9 := by
  rw [cnt_ncard_inter ai_ADot_M2Dot_le_MDot (cnt_sq_of_isEn ADot_M2Dot_isEn) cnt_ADot_M2Dot_coe]
  decide +kernel

end

end CFSG.Quasithin.SimsF5
