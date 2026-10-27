module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL3Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo.Sec4.Item434CharThree
open Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)

section Torus

variable {K : Type} [Field K]

@[expose] def torusL3 {s t : K} (h : s * t = 1) : SL(3, K) :=
  ⟨!![s, 0, 0; 0, 1, 0; 0, 0, t], by simp [det_fin_three, h]⟩

theorem torusL3_mul_uSL {s t : K} (h : s * t = 1) (a b c : K) :
    torusL3 h * uSL a b c = uSL (s * a) (s * b) (s ^ 2 * c) * torusL3 h := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusL3, coe_uSL, CFSG.SectionRank.OddCover.u3Mat, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    first
    | linear_combination (-(s * c)) * h
    | linear_combination (-b) * h

theorem torusL3_conj_uSL {s t : K} (h : s * t = 1) (a b c : K) :
    torusL3 h * uSL a b c * (torusL3 h)⁻¹ = uSL (s * a) (s * b) (s ^ 2 * c) := by
  rw [torusL3_mul_uSL h, mul_assoc, mul_inv_cancel, mul_one]

variable [CharP K 3]

theorem not_mem_zpowers_uSL {s : K} (hs0 : s ≠ 0) (hs4 : s ^ 4 ≠ 1) {a b c : K}
    (hq : uSL a b c ≠ 1) : uSL (s * a) (s * b) (s ^ 2 * c) ∉ Subgroup.zpowers (uSL a b c) := by
  intro hmem
  have hq' : ¬ (a = 0 ∧ b = 0 ∧ c = 0) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact hq uSL_zero
  apply hs4
  rcases mem_zpowers_cases_of_pow_three (uSL_pow_three a b c) hmem with h | h | h
  ·
    obtain ⟨h1, h2, h3⟩ := uSL_inj (h.trans uSL_zero.symm)
    exact absurd ⟨(mul_eq_zero.mp h1).resolve_left hs0, (mul_eq_zero.mp h2).resolve_left hs0,
      (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 hs0)⟩ hq'
  ·
    obtain ⟨h1, h2, h3⟩ := uSL_inj h
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · have hc : c ≠ 0 := fun hc => hq' ⟨ha, hb, hc⟩
        have hs2 : s ^ 2 = 1 := by
          have h4 : (s ^ 2 - 1) * c = 0 := by linear_combination h3
          linear_combination (mul_eq_zero.mp h4).resolve_right hc
        linear_combination (s ^ 2 + 1) * hs2
      · have h4 : (s - 1) * b = 0 := by linear_combination h2
        have hs1 : s = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hb)
        rw [hs1]
        norm_num
    · have h4 : (s - 1) * a = 0 := by linear_combination h1
      have hs1 : s = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right ha)
      rw [hs1]
      norm_num
  ·
    rw [uSL_inv] at h
    obtain ⟨h1, h2, h3⟩ := uSL_inj h
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · have hc : c ≠ 0 := fun hc => hq' ⟨ha, hb, hc⟩
        have hs2 : s ^ 2 = -1 := by
          have h4 : (s ^ 2 + 1) * c = 0 := by linear_combination h3 + b * ha
          linear_combination (mul_eq_zero.mp h4).resolve_right hc
        linear_combination (s ^ 2 - 1) * hs2
      · have h4 : (s + 1) * b = 0 := by linear_combination h2
        have hs1 : s = -1 := eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h4).resolve_right hb)
        rw [hs1]
        norm_num
    · have h4 : (s + 1) * a = 0 := by linear_combination h1
      have hs1 : s = -1 := eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h4).resolve_right ha)
      rw [hs1]
      norm_num

theorem exists_torusL3_witness {s t : K} (h : s * t = 1) (hs0 : s ≠ 0) (hs4 : s ^ 4 ≠ 1)
    {q : SL(3, K)} (hq : q ∈ heis K) (hq1 : q ≠ 1) :
    ∃ g : SL(3, K), (g * q * g⁻¹) * q = q * (g * q * g⁻¹) ∧ g * q * g⁻¹ ∉ Subgroup.zpowers q := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c : K, q = uSL a b c := hq
  refine ⟨torusL3 h, ?_, ?_⟩
  · rw [torusL3_conj_uSL h]
    exact (uSL_commute_iff (s * a) (s * b) (s ^ 2 * c) a b c).mpr (by ring)
  · rw [torusL3_conj_uSL h]
    exact not_mem_zpowers_uSL hs0 hs4 hq1

end Torus

theorem not_three_pow_succ_dvd_card_SL_three {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : Nat.card K = 3 ^ m) (hm0 : m ≠ 0) : ¬ 3 ^ (3 * m + 1) ∣ Nat.card SL(3, K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3), hm,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num),
    show 3 * (3 - 1) / 2 = 3 by norm_num]
  intro hdvd
  have h3m : 3 ∣ 3 ^ m := dvd_pow_self 3 hm0
  have h3sq : 3 ∣ (3 ^ m) ^ 2 := dvd_pow h3m two_ne_zero
  have h3cube : 3 ∣ (3 ^ m) ^ 3 := dvd_pow h3m (by norm_num)
  have hsq : 1 ≤ (3 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hcu : 1 ≤ (3 ^ m) ^ 3 := Nat.one_le_pow _ _ (by positivity)
  have key : 3 ^ (3 * m + 1) = (3 ^ m) ^ 3 * 3 := by ring
  rw [key] at hdvd
  have hX : 3 ∣ ((3 ^ m) ^ 2 - 1) * ((3 ^ m) ^ 3 - 1) :=
    (mul_dvd_mul_iff_left (by positivity : (3 ^ m) ^ 3 ≠ 0)).mp hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hX with h | h <;> omega

instance finite_SL_three_c3 (K : Type) [Field K] [Finite K] : Finite SL(3, K) :=
  Finite.of_injective (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K))
    Subtype.val_injective

instance finite_projSL_three_c3 (K : Type) [Field K] [Finite K] : Finite (projSL 3 K) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem listRow_SL_three_char_three {K : Type} [Field K] [Finite K] [CharP K 3]
    (h9 : 9 ≤ Nat.card K) : ListRow SL(3, K) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨e, he⟩ := FiniteField.card K 3
  have hcard : Nat.card K = 3 ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, he.2]
  have he0 : (e : ℕ) ≠ 0 := e.ne_zero
  obtain ⟨s, hs⟩ : ∃ s : Kˣ, s ^ 4 ≠ 1 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    refine ⟨g, fun h4 => ?_⟩
    have h1 : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [Nat.card_units] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h4
    have h3 : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hQ : Nat.card (heis K) = 3 ^ (3 * (e : ℕ)) := by
    rw [card_heis, hcard, ← pow_mul, mul_comm]
  have hS := not_three_pow_succ_dvd_card_SL_three hcard he0
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  refine not_weaklyClosed_of_sylow_witness (3 * (e : ℕ)) (heis K) hQ hS (fun q hq hqo => ?_) hz
  have hq1 : q ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hqo
    omega
  exact exists_torusL3_witness (Units.mul_inv s) (Units.ne_zero s)
    (fun h4 => hs (Units.ext (by simpa using h4))) hq hq1

theorem listRow_projSL_three_char_three {K : Type} [Field K] [Finite K] [CharP K 3]
    (h9 : 9 ≤ Nat.card K) : ListRow (projSL 3 K) :=
  ListRow.of_mulEquiv (slEquivProjSL K) (listRow_SL_three_char_three h9)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
