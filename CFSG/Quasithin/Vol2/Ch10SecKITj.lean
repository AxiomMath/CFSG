module

public import CFSG.Quasithin.Vol2.Ch10SecKITi
public import CFSG.Quasithin.Vol2.Ch10SecKIK2t
public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch11.SecA (oSL2 BarData)
open CFSG.Quasithin.Vol2.Ch10.SecC.C10KH (isPSL_of_top)

variable {Y : Type} [Group Y]

theorem isSL3_of_top {q : ℕ} (h : IsSL3 q ↥(⊤ : Subgroup Y)) : IsSL3 q Y := by
  obtain ⟨K, hK, hKf, hq, ⟨e⟩⟩ := h
  exact ⟨K, hK, hKf, hq, ⟨Subgroup.topEquiv.symm.trans e⟩⟩

theorem isPSp4_of_top {p e : ℕ} (h : IsPSp4 p e ↥(⊤ : Subgroup Y)) : IsPSp4 p e Y := by
  obtain ⟨hadm, K, hF, hfin, hK, ⟨f⟩⟩ := h
  exact ⟨hadm, K, hF, hfin, hK, ⟨Subgroup.topEquiv.symm.trans f⟩⟩

theorem eq_of_card_eq {a b n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f)
    (h : 2 ^ a * oSL2 n = 2 ^ b * oSL2 f) : a = b ∧ n = f := by
  have h1 := Ch11.SecA.odd_oSL2 hn
  have h2 := Ch11.SecA.odd_oSL2 hf
  refine ⟨Ch11.SecA.eq_of_two_pow_mul_odd h1 h2 h, ?_⟩
  have h3 := Ch11.SecA.eq_of_two_pow_mul_eq h1 h2 h
  unfold oSL2 at h3
  have h4 : 2 ^ (2 * n) = 2 ^ (2 * f) := by
    have := Nat.one_le_two_pow (n := 2 * n)
    have := Nat.one_le_two_pow (n := 2 * f)
    omega
  have := Nat.pow_right_injective (le_refl 2) h4
  omega

theorem not_isPGroup_of_card {H : Type} [Group H] [Finite H] {a n : ℕ} (hn : 1 ≤ n)
    (h : Nat.card H = 2 ^ a * oSL2 n) : ¬ IsPGroup 2 H := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [h] at hk
  have hodd := Ch11.SecA.odd_oSL2 hn
  have h3 : oSL2 n ∣ 2 ^ k := hk ▸ dvd_mul_left _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have h5 : 3 ≤ oSL2 n := by
    unfold oSL2
    have : 2 ^ 2 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases j with _ | j
  · rw [hj] at h5
    norm_num at h5
  · rw [hj, pow_succ] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)

variable [Finite Y]

omit [Finite Y] in
theorem false_of_le_L32 {B : Subgroup Y} {n a : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 1 Y ∨ IsSL3 (2 ^ 1) Y) (hB : Nat.card ↥B = 2 ^ a * oSL2 n) : False := by
  have h168 : Nat.card Y = 168 := by
    rcases hY with hY | ⟨K, _, _, hK, ⟨e⟩⟩
    · rw [Ch11.SecA.card_of_isPSL (by norm_num) hY]
      decide
    · have := Fintype.ofFinite K
      rw [Nat.card_congr (e.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
        Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
      simp [Fin.prod_univ_three]
  have hdvd : oSL2 n ∣ 168 := by
    rw [← h168]
    exact (dvd_mul_left _ _).trans (hB ▸ Subgroup.card_subgroup_dvd_card B)
  have hodd := Ch11.SecA.odd_oSL2 (m := n) (by omega)
  have h2 : Nat.Coprime 2 (oSL2 n) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd.not_two_dvd_nat
  have h8 : Nat.Coprime (oSL2 n) (2 ^ 3) := (Nat.Coprime.pow_left 3 h2).symm
  have e168 : (168 : ℕ) = 2 ^ 3 * 21 := by norm_num
  rw [e168] at hdvd
  have h21 : oSL2 n ∣ 21 := (Nat.Coprime.dvd_mul_left h8).mp hdvd
  have hle : oSL2 n ≤ 21 := Nat.le_of_dvd (by norm_num) h21
  have h63 : n < 3 := by
    by_contra hc
    have : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold oSL2 at hle
    omega
  have : n = 2 := by omega
  subst this
  exact absurd h21 (by decide)

theorem lie_case (hLF : Ch10.A312LeviField) (hK1 : KGRank2ParabolicOrder) {B : Subgroup Y}
    {n : ℕ} (hn : 2 ≤ n) (hC2 : A312C2 B ⊤) (hAb : AbO2 ↥B)
    (hT : Nat.card ↥B = 2 ^ (3 * n) * oSL2 n ∨ Nat.card ↥B = 2 ^ n * oSL2 n) :
    (IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) ∧ Nat.card ↥B = 2 ^ (3 * n) * oSL2 n := by
  obtain ⟨f, k, -, -, hfam⟩ := hLF Y B ⊤ hC2
  obtain ⟨-, -, P, hP, hBP⟩ := hC2
  have hAbP : AbO2 ↥(perfectCore P) := hBP ▸ hAb
  rcases hfam with ⟨hf, hY⟩ | ⟨hf, hY⟩ | ⟨hf, hY⟩ | ⟨hf, hY⟩ | ⟨hf, hY⟩ | ⟨hodd, hf, hY⟩
  ·
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      rcases hT with h | h <;> exact (false_of_le_L32 hn (Or.inl (isPSL_of_top hY)) h).elim
    · have hc := (hK1 Y f hf2 P hP).1 (Or.inl (isPSL_of_top hY))
      rw [← hBP] at hc
      rcases hT with h | h
      · obtain ⟨-, rfl⟩ := eq_of_card_eq (by omega) (by omega) (h.symm.trans hc)
        exact ⟨Or.inl (isPSL_of_top hY), h⟩
      · obtain ⟨h1, h2⟩ := eq_of_card_eq (by omega) (by omega) (h.symm.trans hc)
        omega
  ·
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      rcases hT with h | h <;> exact (false_of_le_L32 hn (Or.inr (isSL3_of_top hY)) h).elim
    · have hc := (hK1 Y f hf2 P hP).1 (Or.inr (isSL3_of_top hY))
      rw [← hBP] at hc
      rcases hT with h | h
      · obtain ⟨-, rfl⟩ := eq_of_card_eq (by omega) (by omega) (h.symm.trans hc)
        exact ⟨Or.inr (isSL3_of_top hY), h⟩
      · obtain ⟨h1, h2⟩ := eq_of_card_eq (by omega) (by omega) (h.symm.trans hc)
        omega
  ·
    have hc := (hK1 Y f hf P hP).2 (isPSp4_of_top hY)
    rw [← hBP] at hc
    exfalso
    rcases hT with h | h
    · obtain ⟨h1, h2⟩ := eq_of_card_eq (by omega) (by omega) (h.symm.trans hc)
      omega
    · obtain ⟨h1, h2⟩ := eq_of_card_eq (by omega) (by omega) (h.symm.trans hc)
      omega
  · exact (not_abO2_perfectCore_g2 ⊤ P f hf hY hP hAbP).elim
  · exact (not_abO2_perfectCore_d4 ⊤ P f hf hY hP hAbP).elim
  · exact (not_abO2_perfectCore_f4 ⊤ P f hodd hf hY hP hAbP).elim

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
