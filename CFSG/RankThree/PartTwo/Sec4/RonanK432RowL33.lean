module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Char3List
public import CFSG.RankThree.PartTwo.Sec4.Item49Small

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434CharThree
open Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)

section Swap

variable {K : Type} [Field K]

@[expose] def swapL3 : SL(3, K) :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem swapL3_mul_uSL (c : K) : swapL3 * uSL 0 0 c = uSL (-c) 0 0 * swapL3 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapL3, coe_uSL, CFSG.SectionRank.OddCover.u3Mat, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

theorem swapL3_conj_uSL (c : K) : swapL3 * uSL 0 0 c * swapL3⁻¹ = uSL (-c) 0 0 := by
  rw [swapL3_mul_uSL, mul_assoc, mul_inv_cancel, mul_one]

end Swap

section Centre

variable {K : Type} [Field K]

theorem eq_zero_of_central_heis {a b c : K} (hc : ∀ q ∈ heis K, q * uSL a b c = uSL a b c * q) :
    a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    have h := (uSL_commute_iff (1 : K) 0 0 a b c).mp (hc (uSL 1 0 0) ⟨1, 0, 0, rfl⟩)
    simpa using h
  have ha : a = 0 := by
    have h := (uSL_commute_iff (0 : K) 1 0 a b c).mp (hc (uSL 0 1 0) ⟨0, 1, 0, rfl⟩)
    simpa using h.symm
  exact ⟨ha, hb⟩

theorem uSL_neg_not_mem_zpowers [CharP K 3] {c : K} (hc : c ≠ 0) :
    uSL (-c) 0 0 ∉ Subgroup.zpowers (uSL 0 0 c) := by
  intro hmem
  rcases mem_zpowers_cases_of_pow_three (uSL_pow_three 0 0 c) hmem with h | h | h
  · obtain ⟨h1, -, -⟩ := uSL_inj (h.trans uSL_zero.symm)
    exact hc (neg_eq_zero.mp h1)
  · obtain ⟨h1, -, -⟩ := uSL_inj h
    exact hc (neg_eq_zero.mp h1)
  · rw [uSL_inv] at h
    obtain ⟨h1, -, -⟩ := uSL_inj h
    exact hc (neg_eq_zero.mp (h1.trans neg_zero))

theorem exists_swapL3_witness [CharP K 3] {c : K} (hc : c ≠ 0) :
    ∃ g : SL(3, K), (g * uSL 0 0 c * g⁻¹) * uSL 0 0 c = uSL 0 0 c * (g * uSL 0 0 c * g⁻¹) ∧
      g * uSL 0 0 c * g⁻¹ ∉ Subgroup.zpowers (uSL 0 0 c) := by
  refine ⟨swapL3, ?_⟩
  rw [swapL3_conj_uSL]
  exact ⟨(uSL_commute_iff _ _ _ _ _ _).mpr (by ring), uSL_neg_not_mem_zpowers hc⟩

end Centre

theorem listRow_SL_three_char_three_card {K : Type} [Field K] [Finite K] [CharP K 3] {m : ℕ}
    (hm : Nat.card K = 3 ^ m) (hm0 : m ≠ 0) : ListRow SL(3, K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Nat.card (heis K) = 3 ^ (3 * m) := by rw [card_heis, hm]; ring
  refine listRow_of_sylow_center (3 * m) (heis K) hQ
    (not_three_pow_succ_dvd_card_SL_three hm hm0) ?_
  intro u hu huo hcomm
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : K, u = uSL a b c := hu
  obtain ⟨rfl, rfl⟩ := eq_zero_of_central_heis hcomm
  have hc : c ≠ 0 := by
    rintro rfl
    rw [uSL_zero, orderOf_one] at huo
    norm_num at huo
  exact exists_swapL3_witness hc

theorem listRow_projSL_three_gf_three : ListRow (projSL 3 (GaloisField 3 1)) :=
  ListRow.of_mulEquiv (slEquivProjSL (GaloisField 3 1))
    (listRow_SL_three_char_three_card (m := 1) (GaloisField.card 3 1 (by norm_num)) one_ne_zero)

theorem outerRow_projSL_three_gf_three : OuterRow (projSL 3 (GaloisField 3 1)) :=
  outerRow_of_not_three_dvd_outer
    (CFSG.RankThree.PartTwo.Sec4.Item49Small.not_three_dvd_card_outer_projSL (n := 3) (e := 1)
      (by norm_num) (by norm_num) (by norm_num))

theorem goodRow_projSL_three_gf_three : GoodRow (projSL 3 (GaloisField 3 1)) :=
  ⟨listRow_projSL_three_gf_three, outerRow_projSL_three_gf_three⟩

theorem rowOf_nine_SL3_one : RowOf (projSL 3 (GaloisField 3 1)) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv e.symm goodRow_projSL_three_gf_three

end CFSG.RankThree.PartTwo.Sec4.RonanK432
