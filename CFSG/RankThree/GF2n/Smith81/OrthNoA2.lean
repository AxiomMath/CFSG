module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Smith81.OrthTensorModel
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem orthE2_isCoprime_pow_sub_one (q : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    IsCoprime (q ^ k - 1) q := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨-1, q ^ j, by ring⟩

theorem orthE2_isCoprime_pow_add_one (q : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    IsCoprime (q ^ k + 1) q := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨1, -q ^ j, by ring⟩

theorem orthE2_exp_eq {q : ℤ} (hq : 2 ≤ q) {a b : ℕ} {T T' : ℤ}
    (hT : IsCoprime T q) (hT' : IsCoprime T' q) (h : q ^ a * T = q ^ b * T') : a = b := by
  have hq0 : q ≠ 0 := by omega
  have key : ∀ (c d : ℕ) (U V : ℤ), IsCoprime U q → q ^ c * U = q ^ d * V → c < d → False := by
    intro c d U V hU hcd hlt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e : q ^ (c + k + 1) = q ^ c * q ^ (k + 1) := by ring
    have hU' : U = q ^ (k + 1) * V := by
      apply mul_left_cancel₀ (pow_ne_zero c hq0)
      rw [hcd, e]
      ring
    have hqU : q ∣ U := by
      rw [hU']
      exact dvd_mul_of_dvd_left (dvd_pow_self q (Nat.succ_ne_zero k)) V
    have hunit : IsUnit q := hU.isUnit_of_dvd' hqU (dvd_refl q)
    rcases Int.isUnit_iff.mp hunit with h1 | h1 <;> omega
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact (key a b T T' hT h hab).elim
  · rfl
  · exact (key b a T' T hT' h.symm hab).elim

theorem orthE2_coprime_pow_sub_one {Q : ℕ} (hQ : 1 ≤ Q) {k : ℕ} (hk : 1 ≤ k) :
    Nat.Coprime (Q ^ k - 1) Q := by
  rw [← Nat.isCoprime_iff_coprime]
  have h1 : 1 ≤ Q ^ k := Nat.one_le_pow _ _ hQ
  have e : ((Q ^ k - 1 : ℕ) : ℤ) = (Q : ℤ) ^ k - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  rw [e]
  exact orthE2_isCoprime_pow_sub_one (Q : ℤ) hk

theorem orthE2_prod_pow_sub (Q n : ℕ) :
    ∏ i : Fin n, (Q ^ n - Q ^ (i : ℕ)) =
      Q ^ (n * (n - 1) / 2) * ∏ i : Fin n, (Q ^ (n - (i : ℕ)) - 1) := by
  have h1 : ∀ i : Fin n, Q ^ n - Q ^ (i : ℕ) = Q ^ (i : ℕ) * (Q ^ (n - (i : ℕ)) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ n := i.2.le
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hi]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

theorem orthE2_card_sl_factor (n : ℕ) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] {q : ℕ}
    (hq : 2 ≤ q) (hK : Nat.card K = q) :
    ∃ T : ℕ, Nat.Coprime T q ∧ Nat.card (StatedSL n K) = q ^ (n * (n - 1) / 2) * T := by
  letI : Fintype K := Fintype.ofFinite K
  haveI : NeZero n := ⟨by omega⟩
  have hcard : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hK]
  have hsl : Nat.card (StatedSL n K) = (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) / (q - 1) := by
    rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, hcard]
  set R : ℕ := ∏ i : Fin n, (q ^ (n - (i : ℕ)) - 1) with hR
  have hdvd : q - 1 ∣ R := by
    have hmem : (⟨n - 1, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_univ _
    have h := Finset.dvd_prod_of_mem (fun i : Fin n => q ^ (n - (i : ℕ)) - 1) hmem
    have e : n - (n - 1) = 1 := by omega
    simpa [e, hR] using h
  have hcop : Nat.Coprime R q := by
    apply Nat.Coprime.prod_left
    intro i _
    exact orthE2_coprime_pow_sub_one (by omega) (by have := i.2; omega)
  refine ⟨R / (q - 1), Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd) hcop, ?_⟩
  rw [hsl, orthE2_prod_pow_sub q n, ← hR, Nat.mul_div_assoc _ hdvd]

theorem orthE2_card_sl_two {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 1 ≤ q)
    (hK : Nat.card K = q) :
    (Nat.card (StatedSL 2 K) : ℤ) = (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
  rw [CFSG.Open.StatedAPI.card_statedSL_two K, hK]
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  push_cast [Nat.cast_sub h2] <;> ring

theorem orthE2_charP_two {K : Type} [Field K] [Finite K] {f : ℕ} (h : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, h]
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 2 ^ f := by
    rw [← hcard, hn]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hpar : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  have hc := ringChar.charP K
  rw [hpar] at hc
  exact hc

theorem orthE2_card_omega_plus_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    (Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) : ℤ) =
      (Nat.card K : ℤ) ^ 2 * ((Nat.card K : ℤ) ^ 2 - 1) ^ 2 := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two K]
  have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  push_cast [Nat.cast_sub h2] <;> ring

theorem orthE2_card_omega_minus_two {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ 2 * ((Nat.card K : ℤ) ^ 4 - 1) := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr]
  have e1 : CFSG.SeitzReduction.F4Pilot.ordSL 2 (Nat.card K ^ 2) =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    simp [CFSG.SeitzReduction.F4Pilot.ordSL, ← pow_mul]
  rw [e1]
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have h4 : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ hK0
  push_cast [Nat.cast_sub h4] <;> ring

theorem orthE2_exists_omega_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) (h4 : 4 ≤ Nat.card K) :
    ∃ T : ℤ, IsCoprime T (Nat.card K : ℤ) ∧
      (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) =
        (Nat.card K : ℤ) ^ (m * (m - 1)) * T := by
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · refine ⟨((Nat.card K : ℤ) ^ 2 - 1) ^ 2,
      IsCoprime.pow_left (orthE2_isCoprime_pow_sub_one (Nat.card K : ℤ) (k := 2) (by norm_num)),
      ?_⟩
    rw [orthE2_card_omega_plus_two h4]
  · refine ⟨((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1), ?_, ?_⟩
    · apply IsCoprime.mul_left
      · exact orthE2_isCoprime_pow_sub_one _ (by omega)
      · apply IsCoprime.prod_left
        intro i hi
        have := (Finset.mem_Icc.mp hi).1
        exact orthE2_isCoprime_pow_sub_one _ (by omega)
    · rw [card_statedOmega_plus_eq hm3]
      ring

theorem orthE2_exists_omega_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ T : ℤ, IsCoprime T (Nat.card K : ℤ) ∧
      (Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) : ℤ) =
        (Nat.card K : ℤ) ^ (m * (m - 1)) * T := by
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · refine ⟨(Nat.card K : ℤ) ^ 4 - 1, orthE2_isCoprime_pow_sub_one _ (by norm_num), ?_⟩
    rw [orthE2_card_omega_minus_two hirr]
  · refine ⟨((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1), ?_, ?_⟩
    · apply IsCoprime.mul_left
      · exact orthE2_isCoprime_pow_add_one _ (by omega)
      · apply IsCoprime.prod_left
        intro i hi
        have := (Finset.mem_Icc.mp hi).1
        exact orthE2_isCoprime_pow_sub_one _ (by omega)
    · rw [card_statedOmega_minus_eq hm3 hirr]
      ring

theorem orthE2_sl_ne {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) {T₁ T₂ : ℤ}
    (hT₁ : IsCoprime T₁ (q : ℤ)) (hT₂ : IsCoprime T₂ (q : ℤ))
    (h : (q : ℤ) ^ (2 * m * (2 * m - 1) / 2) * T₁ =
      (q : ℤ) * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ (m * (m - 1)) * T₂)) : False := by
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hC : IsCoprime ((q : ℤ) ^ 2 - 1) (q : ℤ) := orthE2_isCoprime_pow_sub_one _ (by norm_num)
  have hN : 2 * m * (2 * m - 1) / 2 = m * (2 * m - 1) := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  have h' : (q : ℤ) ^ (2 * m * (2 * m - 1) / 2) * T₁ =
      (q : ℤ) ^ (1 + m * (m - 1)) * (((q : ℤ) ^ 2 - 1) * T₂) := by
    rw [h, pow_add]
    ring
  have hexp := orthE2_exp_eq hq' hT₁ (IsCoprime.mul_left hC hT₂) h'
  rw [hN] at hexp
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e1 : (k + 2) * (2 * (k + 2) - 1) = (k + 2) * (2 * k + 3) := by
    rw [show 2 * (k + 2) - 1 = 2 * k + 3 by omega]
  have e2 : k + 2 - 1 = k + 1 := by omega
  rw [e1, e2] at hexp
  nlinarith [hexp]

theorem orthE2_card_absurd {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q) {A B : ℕ} {T₂ : ℤ}
    (hA : (A : ℤ) = (q : ℤ) * ((q : ℤ) ^ 2 - 1))
    (hT₂ : IsCoprime T₂ (q : ℤ)) (hB : (B : ℤ) = (q : ℤ) ^ (m * (m - 1)) * T₂)
    (hsl : Nat.card (StatedSL (2 * m) K) = A * B) : False := by
  obtain ⟨T, hTc, hTeq⟩ := orthE2_card_sl_factor (2 * m) (by omega) hq hK
  have h1 : ((Nat.card (StatedSL (2 * m) K) : ℕ) : ℤ) = ((A * B : ℕ) : ℤ) := by rw [hsl]
  rw [hTeq] at h1
  push_cast at h1
  rw [hA, hB] at h1
  exact orthE2_sl_ne hq hm (Nat.isCoprime_iff_coprime.mpr hTc) hT₂ h1

theorem orthE2_two_absurd_plus {q : ℕ} (hq : 4 ≤ q)
    (h : (q : ℤ) ^ 3 * (((q : ℤ) ^ 3) ^ 2 - 1) =
      (q : ℤ) * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) ^ 2)) : False := by
  have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have key : (q : ℤ) ^ 5 * (3 * ((q : ℤ) ^ 2 - 1)) = 0 := by linear_combination h
  have hpos : (0 : ℤ) < (q : ℤ) ^ 5 * (3 * ((q : ℤ) ^ 2 - 1)) := by
    apply mul_pos (pow_pos (by linarith) 5)
    nlinarith
  linarith

theorem orthE2_two_absurd_minus {q : ℕ} (hq : 4 ≤ q)
    (h : (q : ℤ) ^ 3 * (((q : ℤ) ^ 3) ^ 2 - 1) =
      (q : ℤ) * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 * ((q : ℤ) ^ 4 - 1))) : False := by
  have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq
  have key : (q : ℤ) ^ 3 * ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 - 2) = 0 := by linear_combination h
  have hpos : (0 : ℤ) < (q : ℤ) ^ 3 * ((q : ℤ) ^ 4 + (q : ℤ) ^ 2 - 2) := by
    apply mul_pos (pow_pos (by linarith) 3)
    nlinarith
  linarith

theorem noA2All_of_caseE2 [Finite G] {M Q Z B : Subgroup G}
    (hc : Cfg M Q Z B) {t : G} {m : ℕ} (hE : CaseE2 M Q Z B t m) : NoA2All M Q Z := by
  obtain ⟨hm2, hQ, -, hsign⟩ := hE
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  have hq1 : 1 ≤ Nat.card Z := by omega
  obtain ⟨f, -, hf, -⟩ := hc.ctx.hyp.cp
  obtain ⟨h1, -⟩ := hc.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, hSS, -⟩ | ⟨-, hA | hVI⟩
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
    have h :=  Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  ·
    exfalso
    have h := Nat.pow_right_injective hq2 (hQ9.symm.trans hQ)
    obtain rfl : m = 2 := by omega
    obtain ⟨hNS3, K₃, fK₃, finK₃, hK₃, ⟨e₃⟩⟩ := hSS
    have hK₃' : Nat.card K₃ = Nat.card Z ^ 3 := hK₃
    rcases hsign with ⟨-, hP⟩ | ⟨-, hP⟩
    · obtain ⟨hNS, A, B', instA, instB, hA, hB, ⟨eAB⟩⟩ := hP
      obtain ⟨K₁, fK₁, finK₁, hK₁, ⟨eA⟩⟩ := hA
      obtain ⟨K₂, fK₂, finK₂, hK₂, ⟨eB⟩⟩ := hB
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      have hAc : (Nat.card A : ℤ) = (Nat.card Z : ℤ) * ((Nat.card Z : ℤ) ^ 2 - 1) := by
        rw [Nat.card_congr eA.toEquiv]
        exact orthE2_card_sl_two hq1 hK₁
      have hBc : (Nat.card B' : ℤ) = (Nat.card Z : ℤ) ^ 2 * ((Nat.card Z : ℤ) ^ 2 - 1) ^ 2 := by
        rw [Nat.card_congr eB.toEquiv,
          orthE2_card_omega_plus_two (K := K₂) (by rw [hK₂]; exact hq4), hK₂]
      have hC : Nat.card (StatedSL 2 K₃) = Nat.card A * Nat.card B' := by
        rw [← Nat.card_congr e₃.toEquiv, Nat.card_congr eAB.toEquiv, Nat.card_prod]
      have hCc : (Nat.card (StatedSL 2 K₃) : ℤ) =
          (Nat.card Z : ℤ) ^ 3 * (((Nat.card Z : ℤ) ^ 3) ^ 2 - 1) := by
        rw [orthE2_card_sl_two (K := K₃) (q := Nat.card Z ^ 3)
          (Nat.one_le_pow _ _ (by omega)) hK₃', Nat.cast_pow]
      have hCAB : (Nat.card (StatedSL 2 K₃) : ℤ) = (Nat.card A : ℤ) * (Nat.card B' : ℤ) := by
        rw [hC, Nat.cast_mul]
      rw [hCc, hAc, hBc] at hCAB
      exact orthE2_two_absurd_plus hq4 hCAB
    · obtain ⟨hNS, A, B', instA, instB, hA, hB, ⟨eAB⟩⟩ := hP
      obtain ⟨K₁, fK₁, finK₁, hK₁, ⟨eA⟩⟩ := hA
      obtain ⟨K₂, fK₂, finK₂, hK₂, b, c, hirr, ⟨eB⟩⟩ := hB
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      have hAc : (Nat.card A : ℤ) = (Nat.card Z : ℤ) * ((Nat.card Z : ℤ) ^ 2 - 1) := by
        rw [Nat.card_congr eA.toEquiv]
        exact orthE2_card_sl_two hq1 hK₁
      have hBc : (Nat.card B' : ℤ) = (Nat.card Z : ℤ) ^ 2 * ((Nat.card Z : ℤ) ^ 4 - 1) := by
        rw [Nat.card_congr eB.toEquiv, orthE2_card_omega_minus_two (K := K₂) hirr, hK₂]
      have hC : Nat.card (StatedSL 2 K₃) = Nat.card A * Nat.card B' := by
        rw [← Nat.card_congr e₃.toEquiv, Nat.card_congr eAB.toEquiv, Nat.card_prod]
      have hCc : (Nat.card (StatedSL 2 K₃) : ℤ) =
          (Nat.card Z : ℤ) ^ 3 * (((Nat.card Z : ℤ) ^ 3) ^ 2 - 1) := by
        rw [orthE2_card_sl_two (K := K₃) (q := Nat.card Z ^ 3)
          (Nat.one_le_pow _ _ (by omega)) hK₃', Nat.cast_pow]
      have hCAB : (Nat.card (StatedSL 2 K₃) : ℤ) = (Nat.card A : ℤ) * (Nat.card B' : ℤ) := by
        rw [hC, Nat.cast_mul]
      rw [hCc, hAc, hBc] at hCAB
      exact orthE2_two_absurd_minus hq4 hCAB
  ·
    exact hA.1
  ·
    exfalso
    obtain ⟨n, hn⟩ : ∃ n, CaseE6 M Q Z B n := hVI
    obtain ⟨V₁, V₂, hL⟩ := CaseE6.exists_linSetup hn
    have hWn : Nat.card Q = Nat.card Z ^ (2 * n + 1) := LinSetup.width hc.ctx.hyp hL
    have hnm : n = 2 * m := by
      have h := Nat.pow_right_injective hq2 (hWn.symm.trans hQ)
      omega
    subst hnm
    obtain ⟨K, fK, finK, hKc, φ, hφr, hφk, -⟩ := hn
    have hquot : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) =
        Nat.card (StatedSL (2 * m) K) := by
      rw [← hφk, ← hφr]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rcases hsign with ⟨-, hP⟩ | ⟨-, hP⟩
    · obtain ⟨hNS, A, B', instA, instB, hA, hB, ⟨eAB⟩⟩ := hP
      obtain ⟨K₁, fK₁, finK₁, hK₁, ⟨eA⟩⟩ := hA
      obtain ⟨K₂, fK₂, finK₂, hK₂, ⟨eB⟩⟩ := hB
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      have hsl : Nat.card (StatedSL (2 * m) K) = Nat.card A * Nat.card B' := by
        rw [← hquot, Nat.card_congr eAB.toEquiv, Nat.card_prod]
      obtain ⟨T₂, hT₂, hBeq⟩ :=
        orthE2_exists_omega_plus (K := K₂) hm2 (by rw [hK₂]; exact hq4)
      rw [hK₂] at hT₂ hBeq
      have hBeq' : (Nat.card B' : ℤ) = (Nat.card Z : ℤ) ^ (m * (m - 1)) * T₂ := by
        rw [Nat.card_congr eB.toEquiv, hBeq]
      have hAc : (Nat.card A : ℤ) = (Nat.card Z : ℤ) * ((Nat.card Z : ℤ) ^ 2 - 1) := by
        rw [Nat.card_congr eA.toEquiv]
        exact orthE2_card_sl_two hq1 hK₁
      exact orthE2_card_absurd hq2 hm2 hKc hAc hT₂ hBeq' hsl
    · obtain ⟨hNS, A, B', instA, instB, hA, hB, ⟨eAB⟩⟩ := hP
      obtain ⟨K₁, fK₁, finK₁, hK₁, ⟨eA⟩⟩ := hA
      obtain ⟨K₂, fK₂, finK₂, hK₂, b, c, hirr, ⟨eB⟩⟩ := hB
      haveI : CharP K₂ 2 := orthE2_charP_two (hK₂.trans hf)
      have hsl : Nat.card (StatedSL (2 * m) K) = Nat.card A * Nat.card B' := by
        rw [← hquot, Nat.card_congr eAB.toEquiv, Nat.card_prod]
      obtain ⟨T₂, hT₂, hBeq⟩ := orthE2_exists_omega_minus (K := K₂) hm2 hirr
      rw [hK₂] at hT₂ hBeq
      have hBeq' : (Nat.card B' : ℤ) = (Nat.card Z : ℤ) ^ (m * (m - 1)) * T₂ := by
        rw [Nat.card_congr eB.toEquiv, hBeq]
      have hAc : (Nat.card A : ℤ) = (Nat.card Z : ℤ) * ((Nat.card Z : ℤ) ^ 2 - 1) := by
        rw [Nat.card_congr eA.toEquiv]
        exact orthE2_card_sl_two hq1 hK₁
      exact orthE2_card_absurd hq2 hm2 hKc hAc hT₂ hBeq' hsl

theorem orthTacit_of_caseE2 [Finite G] {M Q Z B : Subgroup G}
    (hc : Cfg M Q Z B) {t : G} {m : ℕ} (hE : CaseE2 M Q Z B t m)
    (hG : StrothGenByBStatement) :
    ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B') ∧ GenByB M Q B' := by
  intro B' hB'
  have hE' := hE
  obtain ⟨hm2, -⟩ := hE'
  have hno : NoA2 Q Z (LB M Q B') :=
    noA2All_of_caseE2 hc hE B' (by obtain ⟨g, hg⟩ := hB'.conj; exact ⟨g, hg⟩) hB'.le hB'.ne
  exact ⟨hno, hG G M Q Z B' hB' (2 * m) (CaseE2.width hE) (by omega) hno⟩

end CFSG.RankThree.GF2n.Smith81
