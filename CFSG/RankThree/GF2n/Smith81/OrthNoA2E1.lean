module

public import CFSG.RankThree.GF2n.Smith81.OrthNoA2
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Core

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem orthE1_card_quot_mul {R N : Subgroup G} (h : N ≤ R) :
    Nat.card (↥R ⧸ N.subgroupOf R) * Nat.card N = Nat.card R := by
  have h1 := Subgroup.card_mul_index (N.subgroupOf R)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv, mul_comm] at h1
  exact h1

theorem orthE1_quot_dvd {R S N Q : Subgroup G} (hNR : N ≤ R) (hRS : R ≤ S) (hQS : Q ≤ S)
    {q : ℕ} (hN : Nat.card N = Nat.card Q * q) (hQ : 0 < Nat.card Q) :
    Nat.card (↥R ⧸ N.subgroupOf R) * q ∣ Nat.card (↥S ⧸ Q.subgroupOf S) := by
  have h3 : Nat.card R ∣ Nat.card S := Subgroup.card_dvd_of_le hRS
  rw [← orthE1_card_quot_mul hNR, ← orthE1_card_quot_mul hQS, hN] at h3
  apply Nat.dvd_of_mul_dvd_mul_right hQ
  have e : Nat.card (↥R ⧸ N.subgroupOf R) * q * Nat.card Q =
      Nat.card (↥R ⧸ N.subgroupOf R) * (Nat.card Q * q) := by ring
  rw [e]
  exact h3

theorem orthE1_Nt_le_Rt (M L : Subgroup G) (t : G) : Nt M L t ≤ Rt M L t :=
  Subgroup.map_subtype_le _

theorem orthE1_card_plus {X : Type} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} (hK : Nat.card K = q) (h4 : 4 ≤ q)
    (e : X ≃* ↥(StatedOmega (StatedQuadPlus 2 K))) :
    (Nat.card X : ℤ) = (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) ^ 2 := by
  rw [Nat.card_congr e.toEquiv, orthE2_card_omega_plus_two (K := K) (by rw [hK]; exact h4), hK]

theorem orthE1_card_minus {X : Type} [Group X] {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} (hK : Nat.card K = q) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
    (Nat.card X : ℤ) = (q : ℤ) ^ 2 * ((q : ℤ) ^ 4 - 1) := by
  rw [Nat.card_congr e.toEquiv, orthE2_card_omega_minus_two (K := K) hirr, hK]

theorem orthE1_card_sl3 {X : Type} [Group X] {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 3) (hq : 1 ≤ q) (e : X ≃* ↥(StatedSL 2 K)) :
    (Nat.card X : ℤ) = (q : ℤ) ^ 3 * (((q : ℤ) ^ 3) ^ 2 - 1) := by
  rw [Nat.card_congr e.toEquiv, orthE2_card_sl_two (Nat.one_le_pow _ _ (by omega)) hK,
    Nat.cast_pow]

theorem orthE1_not_dvd_plus {q : ℤ} (hq : 4 ≤ q)
    (h : q ^ 2 * (q ^ 2 - 1) ^ 2 * q ∣ q ^ 3 * ((q ^ 3) ^ 2 - 1)) : False := by
  have e1 : q ^ 2 * (q ^ 2 - 1) ^ 2 * q = q ^ 3 * (q ^ 2 - 1) ^ 2 := by ring
  rw [e1] at h
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have h2 : (q ^ 2 - 1) ^ 2 ∣ (q ^ 3) ^ 2 - 1 := (mul_dvd_mul_iff_left hq3).mp h
  have e2 : (q ^ 3) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by ring
  have hpos : 0 < q ^ 2 - 1 := by nlinarith
  rw [e2, show (q ^ 2 - 1) ^ 2 = (q ^ 2 - 1) * (q ^ 2 - 1) by ring] at h2
  have h3 : q ^ 2 - 1 ∣ q ^ 4 + q ^ 2 + 1 := (mul_dvd_mul_iff_left hpos.ne').mp h2
  have h4 : q ^ 2 - 1 ∣ (q ^ 4 + q ^ 2 + 1) - (q ^ 2 - 1) * (q ^ 2 + 2) :=
    dvd_sub h3 (dvd_mul_right _ _)
  have e3 : (q ^ 4 + q ^ 2 + 1) - (q ^ 2 - 1) * (q ^ 2 + 2) = 3 := by ring
  rw [e3] at h4
  have h5 := Int.le_of_dvd (by norm_num) h4
  nlinarith

theorem orthE1_not_dvd_minus {q : ℤ} (hq : 4 ≤ q)
    (h : q ^ 2 * (q ^ 4 - 1) * q ∣ q ^ 3 * ((q ^ 3) ^ 2 - 1)) : False := by
  have e1 : q ^ 2 * (q ^ 4 - 1) * q = q ^ 3 * (q ^ 4 - 1) := by ring
  have e2 : q ^ 3 * ((q ^ 3) ^ 2 - 1) = q ^ 3 * ((q ^ 4 - 1) * q ^ 2 + (q ^ 2 - 1)) := by ring
  rw [e1, e2] at h
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have h2 : q ^ 4 - 1 ∣ (q ^ 4 - 1) * q ^ 2 + (q ^ 2 - 1) := (mul_dvd_mul_iff_left hq3).mp h
  have h3 : q ^ 4 - 1 ∣ q ^ 2 - 1 := by
    have h4 := dvd_sub h2 (dvd_mul_right (q ^ 4 - 1) (q ^ 2))
    have e3 : (q ^ 4 - 1) * q ^ 2 + (q ^ 2 - 1) - (q ^ 4 - 1) * q ^ 2 = q ^ 2 - 1 := by ring
    rwa [e3] at h4
  have hq2 : 16 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q ^ 2 - 1 := by nlinarith
  have h5 := Int.le_of_dvd hpos h3
  nlinarith [sq_nonneg q]

theorem noA2All_of_caseE1_of_not_caseVI [Finite G]
    {M Q Z B : Subgroup G} (hc : Cfg M Q Z B) {t : G} (ht : CtxD4 M Q Z B t) (hE : CaseE1 M Q Z B t)
    (hVI : ¬ CaseVI M Q Z (Lgen M (LB M Q B))) : NoA2All M Q Z := by
  obtain ⟨hQ, hNt, hR⟩ := hE
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  have hq1 : 1 ≤ Nat.card Z := by omega
  obtain ⟨f, -, hf, -⟩ := hc.ctx.hyp.cp
  obtain ⟨h1, -⟩ := hc.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, hSS, -⟩ | ⟨-, hA | hVI'⟩
  ·
    exfalso
    obtain ⟨e⟩ := hL3
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqn
      omega
    have hQ3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hqn]
    have h := Nat.pow_right_injective hq2 (hQ3.symm.trans hQ)
    omega
  ·
    exfalso
    have h := Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  ·
    exfalso
    obtain ⟨hNS3, K₃, fK₃, finK₃, hK₃, ⟨e₃⟩⟩ := hSS
    have hSc := orthE1_card_sl3 hK₃ hq1 e₃
    have hQpos : 0 < Nat.card Q := by rw [hQ]; exact pow_pos (by omega) 9
    have hdvd := orthE1_quot_dvd (orthE1_Nt_le_Rt M (LB M Q B) t)
      (Rt_le_Lgen M (LB M Q B) t) (Q_le_Lgen M Q B) hNt hQpos
    have hZ := Int.natCast_dvd_natCast.mpr hdvd
    push_cast at hZ
    rcases hR with ⟨hNR, K₂, fK₂, finK₂, hK₂, ⟨eR⟩⟩ | ⟨hNR, K₂, fK₂, finK₂, hK₂, b, c, hirr, ⟨eR⟩⟩
    ·
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      rw [orthE1_card_plus hK₂ hq4 eR, hSc] at hZ
      exact orthE1_not_dvd_plus (by exact_mod_cast hq4) hZ
    ·
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      rw [orthE1_card_minus hK₂ hirr eR, hSc] at hZ
      exact orthE1_not_dvd_minus (by exact_mod_cast hq4) hZ
  ·
    exact hA.1
  ·
    exact (hVI hVI').elim

end CFSG.RankThree.GF2n.Smith81
