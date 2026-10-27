module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FN

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem genFitting_eq_or_card_dvd_ch615 {W : Type} [CommGroup W] [Finite W]
    {J : Subgroup (MulAut W)} (h : B56Case1 J) :
    quasithinGenFitting J = J ∨ Nat.card J ∣ 40320 ∨ Nat.card J ∣ 12096 := by
  obtain ⟨-, ⟨⟨-, hcase⟩, -⟩, -⟩ := h
  rcases hcase with h1 | h2 | ⟨k, h3⟩ | h4
  · obtain ⟨T, hT⟩ := exists_isSylowTwoOf J
    rcases h1.2.2 T hT with heq | ⟨-, ⟨n, -, hn8, π, hπ, -⟩ | ⟨K, _, _, hK, π, hπ, -⟩⟩
    · exact Or.inl heq.symm
    · refine Or.inr (Or.inl ?_)
      have h1 := Subgroup.card_dvd_of_surjective hπ
      have h2 : Nat.card (Equiv.Perm (Fin n)) ∣ 40320 := by
        rw [Nat.card_perm, Nat.card_fin]
        exact (Nat.factorial_dvd_factorial hn8).trans (by decide)
      exact h1.trans h2
    · refine Or.inr (Or.inr ?_)
      have h1 := Subgroup.card_dvd_of_surjective hπ
      have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
      have h2 : Nat.card ↥(quasithinG2 K) = 12096 := by
        rw [card_quasithinG2_1527d hK', hK]
        norm_num
      exact h2 ▸ h1
  · exact Or.inl h2.1.symm
  · exact Or.inl h3.1.symm
  · exact Or.inl h4.1.symm

theorem genFitting_eq_ch615 {W : Type} [CommGroup W] [Finite W] {J : Subgroup (MulAut W)}
    (h : B56Case1 J) (h1 : ¬ Nat.card (quasithinGenFitting J) ∣ 40320)
    (h2 : ¬ Nat.card (quasithinGenFitting J) ∣ 12096) : quasithinGenFitting J = J := by
  have hdvd : Nat.card (quasithinGenFitting J) ∣ Nat.card J :=
    Subgroup.card_dvd_of_le (quasithinGenFitting_le J)
  rcases genFitting_eq_or_card_dvd_ch615 h with h | h | h
  · exact h
  · exact absurd (hdvd.trans h) h1
  · exact absurd (hdvd.trans h) h2

theorem card_sl3_ge_ch615 {K : Type*} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    60480 ≤ Nat.card SL(3, K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  set q := Nat.card K with hq
  have hq1 : 1 ≤ q - 1 := by omega
  have e1 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_one]
    ring_nf
  rw [e1, show (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 2 * (q - 1)) =
    ((q ^ 3 - 1) * (q ^ 3 - q) * q ^ 2) * (q - 1) by ring, Nat.mul_div_cancel _ (by omega)]
  have h3 : 63 ≤ q ^ 3 - 1 := by
    have : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hK 3
    omega
  have h4 : 60 ≤ q ^ 3 - q := by
    have : q ^ 3 = q * q ^ 2 := by ring
    have h16 : 16 ≤ q ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hK 2
    have : q * 16 ≤ q * q ^ 2 := Nat.mul_le_mul_left q h16
    omega
  have h5 : 16 ≤ q ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hK 2
  calc 60480 = 63 * 60 * 16 := by norm_num
    _ ≤ (q ^ 3 - 1) * (q ^ 3 - q) * q ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 h4) h5

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_case1_sl3_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H)))) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K)) : False := by
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hK4 := exists_finset_four_ch615 h4
  have hcard : 60480 ≤ Nat.card (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    rw [Nat.card_congr e'.toEquiv]
    exact card_sl3_ge_ch615 h4
  have hJ := genFitting_eq_ch615 h1 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  have hB := borelFacts_of_mulEquiv_ch615 e' (not_isSolvable_sl3_ch615 hK4)
    (borel_of_sylow_ch615 (isSylowTwoOf_unitriangular_ch615 hK (by norm_num))
      fun R hUR hR => borel_unitriangular_ch615 hK4 hUR hR)
  exact c.false_of_case1_borel_ch615 hU hJ hB.2

theorem not_dvd_card_sl2_ch615 {m : ℕ} (hm : 4 ≤ m) :
    ¬ 2 ^ m * ((2 ^ m) ^ 2 - 1) ∣ 40320 ∧ ¬ 2 ^ m * ((2 ^ m) ^ 2 - 1) ∣ 12096 := by
  rcases Nat.lt_or_ge m 6 with h | h
  · interval_cases m <;> decide
  · have h64 : 64 ≤ 2 ^ m := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    have h4095 : 4095 ≤ (2 ^ m) ^ 2 - 1 := by
      have : 4096 ≤ (2 ^ m) ^ 2 := by
        calc 4096 = 64 ^ 2 := by norm_num
          _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h64 2
      omega
    have hbig : 40320 < 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      calc 40320 < 64 * 4095 := by norm_num
        _ ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h64 h4095
    exact ⟨fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (by omega),
      fun hd => absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)⟩

theorem false_of_case1_sl2_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H)))) {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 4 ≤ m) (hK : Nat.card K = 2 ^ m)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : False := by
  set e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK4 := exists_finset_four_ch615 h4
  have hcard : Nat.card (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) =
      2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr e'.toEquiv, card_sl2_field_ch615, hK]
  obtain ⟨hd1, hd2⟩ := not_dvd_card_sl2_ch615 hm
  have hJ := genFitting_eq_ch615 h1 (hcard ▸ hd1) (hcard ▸ hd2)
  have hB := borelFacts_of_mulEquiv_ch615 e' (not_isSolvable_sl2_ch615 hK4)
    (borel_of_sylow_ch615 (isSylowTwoOf_unipSub_ch615 hK)
      fun R hUR hR => borel_unipSub_ch615 hK4 hUR hR)
  exact c.false_of_case1_borel_ch615 hU hJ hB.2

end Cx615C

end CFSG.Quasithin.H13
