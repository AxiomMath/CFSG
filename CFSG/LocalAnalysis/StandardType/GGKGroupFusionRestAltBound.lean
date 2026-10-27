module

public import CFSG.RankThree.PartOne.FLM.OrdSmall

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.S12K (charTwoOrder)

theorem ggPow_add_one_le {q : ℕ} (hq : 2 ≤ q) (a : ℕ) : q ^ a + 1 ≤ q ^ (a + 1) := by
  have h1 : 1 ≤ q ^ a := Nat.one_le_pow _ _ (by omega)
  calc q ^ a + 1 ≤ q ^ a * 2 := by omega
    _ ≤ q ^ a * q := Nat.mul_le_mul_left _ hq
    _ = q ^ (a + 1) := (pow_succ q a).symm

theorem ggTwoPow_three_mul (f e : ℕ) : 2 ^ (3 * (f * e)) = (2 ^ f) ^ (3 * e) := by
  rw [← pow_mul]
  congr 1
  ring

theorem ggTwo_le_two_pow {f : ℕ} (hf : 1 ≤ f) : 2 ≤ 2 ^ f :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem ggOrdA_le {n q : ℕ} (hq : 1 ≤ q) : ordA n q ≤ q ^ (3 * (n * (n + 1) / 2)) := by
  set T := n * (n + 1) / 2 with hT
  have hT2 : (n + 1) * n = 2 * T := by
    rw [hT, mul_comm]
    exact (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
  have hP : ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) ≤ (q ^ (n + 1)) ^ n := by
    have h := Finset.prod_le_pow_card (Finset.Icc 2 (n + 1)) (fun i => q ^ i - 1)
      (q ^ (n + 1)) (fun i hi =>
        le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hq (Finset.mem_Icc.mp hi).2))
    rwa [Nat.card_Icc, show n + 1 + 1 - 2 = n by omega] at h
  calc ordA n q ≤ q ^ T * ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) := by
        rw [ordA]
        exact Nat.div_le_self _ _
    _ ≤ q ^ T * (q ^ (n + 1)) ^ n := Nat.mul_le_mul_left _ hP
    _ = q ^ (3 * T) := by
        rw [← pow_mul, ← pow_add, hT2]
        congr 1
        ring

theorem ggTwistedA_factor_le {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat ≤ q ^ (i + 1) := by
  rcases Nat.even_or_odd i with hi | hi
  · rw [toNat_pow_sub_neg_one_pow_of_even (by omega) hi]
    exact le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [toNat_pow_sub_neg_one_pow_of_odd hi]
    exact ggPow_add_one_le hq i

theorem ggProd_twistedA_le {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    ∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat ≤ q ^ (n * (n + 1)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show (1 + 1 : ℕ) = 2 by rfl, Finset.Icc_self, Finset.prod_singleton,
      toNat_pow_sub_neg_one_pow_of_even (by omega) even_two, one_mul]
    exact Nat.sub_le _ _
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1 + 1)]
    calc (∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat) *
          ((q : ℤ) ^ (n + 1 + 1) - (-1) ^ (n + 1 + 1)).toNat
        ≤ q ^ (n * (n + 1)) * q ^ (n + 1 + 1 + 1) :=
          Nat.mul_le_mul ih (ggTwistedA_factor_le hq _)
      _ = q ^ (n * (n + 1) + (n + 3)) := by rw [← pow_add]
      _ ≤ q ^ ((n + 1) * (n + 1 + 1)) :=
          Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem ggOrdTwistedA_le {n q : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) :
    ordTwistedA n q ≤ q ^ (3 * (n * (n + 1) / 2)) := by
  set T := n * (n + 1) / 2 with hT
  have hT2 : n * (n + 1) = 2 * T := by
    rw [hT]
    exact (Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd).symm
  calc ordTwistedA n q
      ≤ q ^ T * ∏ i ∈ Finset.Icc 2 (n + 1), ((q : ℤ) ^ i - (-1) ^ i).toNat := by
        rw [ordTwistedA]
        exact Nat.div_le_self _ _
    _ ≤ q ^ T * q ^ (n * (n + 1)) := Nat.mul_le_mul_left _ (ggProd_twistedA_le hq hn)
    _ = q ^ (3 * T) := by
        rw [← pow_add, hT2]
        congr 1
        ring

theorem ggOrdBC_le {n q : ℕ} (hq : 1 ≤ q) : ordBC n q ≤ q ^ (3 * (n * n)) := by
  have hP : ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) ≤ (q ^ (2 * n)) ^ n := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 n) (fun i => q ^ (2 * i) - 1)
      (q ^ (2 * n)) (fun i hi =>
        le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hq (by
          have := (Finset.mem_Icc.mp hi).2
          omega)))
    rwa [Nat.card_Icc, show n + 1 - 1 = n by omega] at h
  calc ordBC n q ≤ q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) := by
        rw [ordBC]
        exact Nat.div_le_self _ _
    _ ≤ q ^ (n * n) * (q ^ (2 * n)) ^ n := Nat.mul_le_mul_left _ hP
    _ = q ^ (3 * (n * n)) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

theorem ggProd_orthogonal_le {n q : ℕ} (hq : 1 ≤ q) :
    ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) ≤ (q ^ (2 * (n - 1))) ^ (n - 1) := by
  have h := Finset.prod_le_pow_card (Finset.Icc 1 (n - 1)) (fun i => q ^ (2 * i) - 1)
    (q ^ (2 * (n - 1))) (fun i hi =>
      le_trans (Nat.sub_le _ _) (Nat.pow_le_pow_right hq (by
        have := (Finset.mem_Icc.mp hi).2
        omega)))
  rwa [Nat.card_Icc, show n - 1 + 1 - 1 = n - 1 by omega] at h

theorem ggOrdD_le {n q : ℕ} (hq : 1 ≤ q) (hn : 2 ≤ n) :
    ordD n q ≤ q ^ (3 * (n * (n - 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  rw [show k + 1 - 1 = k by omega]
  calc ordD (k + 1) q
      ≤ q ^ ((k + 1) * k) * (q ^ (k + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1) := by
        rw [ordD, show k + 1 - 1 = k by omega]
        exact Nat.div_le_self _ _
    _ ≤ q ^ ((k + 1) * k) * q ^ (k + 1) * (q ^ (2 * k)) ^ k := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) ?_
        simpa using ggProd_orthogonal_le (n := k + 1) hq
    _ = q ^ ((k + 1) * k + (k + 1) + 2 * k * k) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ q ^ (3 * ((k + 1) * k)) := Nat.pow_le_pow_right hq (by nlinarith)

theorem ggOrdTwistedD_le {n q : ℕ} (hq : 2 ≤ q) (hn : 3 ≤ n) :
    ordTwistedD n q ≤ q ^ (3 * (n * (n - 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  have hq1 : 1 ≤ q := by omega
  rw [show k + 1 - 1 = k by omega]
  calc ordTwistedD (k + 1) q
      ≤ q ^ ((k + 1) * k) * (q ^ (k + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 k, (q ^ (2 * i) - 1) := by
        rw [ordTwistedD, show k + 1 - 1 = k by omega]
        exact Nat.div_le_self _ _
    _ ≤ q ^ ((k + 1) * k) * q ^ (k + 1 + 1) * (q ^ (2 * k)) ^ k := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (ggPow_add_one_le hq _)) ?_
        simpa using ggProd_orthogonal_le (n := k + 1) hq1
    _ = q ^ ((k + 1) * k + (k + 1 + 1) + 2 * k * k) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ q ^ (3 * ((k + 1) * k)) := Nat.pow_le_pow_right hq1 (by nlinarith)

theorem ggOrdG2_le {q : ℕ} (hq : 1 ≤ q) : ordG2 q ≤ q ^ (3 * 6) := by
  calc ordG2 q ≤ q ^ 6 * q ^ 6 * q ^ 2 := by
        rw [ordG2]
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 14 := by ring
    _ ≤ q ^ (3 * 6) := Nat.pow_le_pow_right hq (by norm_num)

theorem ggOrdF4_le {q : ℕ} (hq : 1 ≤ q) : ordF4 q ≤ q ^ (3 * 24) := by
  calc ordF4 q ≤ q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
        rw [ordF4]
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 52 := by ring
    _ ≤ q ^ (3 * 24) := Nat.pow_le_pow_right hq (by norm_num)

theorem ggOrdE6_le {q : ℕ} (hq : 1 ≤ q) : ordE6 q ≤ q ^ (3 * 36) := by
  calc ordE6 q ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 5 - 1) * (q ^ 2 - 1) := by
        rw [ordE6]
        exact Nat.div_le_self _ _
    _ ≤ q ^ 36 * q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 78 := by ring
    _ ≤ q ^ (3 * 36) := Nat.pow_le_pow_right hq (by norm_num)

theorem ggOrdTwistedE6_le {q : ℕ} (hq : 2 ≤ q) : ordTwistedE6 q ≤ q ^ (3 * 36) := by
  calc ordTwistedE6 q ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 5 + 1) * (q ^ 2 - 1) := by
        rw [ordTwistedE6]
        exact Nat.div_le_self _ _
    _ ≤ q ^ 36 * q ^ 12 * q ^ (9 + 1) * q ^ 8 * q ^ 6 * q ^ (5 + 1) * q ^ 2 := by
        gcongr
        all_goals first | exact Nat.sub_le _ _ | exact ggPow_add_one_le hq _
    _ = q ^ 80 := by ring
    _ ≤ q ^ (3 * 36) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem ggOrdE7_le {q : ℕ} (hq : 1 ≤ q) : ordE7 q ≤ q ^ (3 * 63) := by
  calc ordE7 q ≤ q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
        (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
        rw [ordE7]
        exact Nat.div_le_self _ _
    _ ≤ q ^ 63 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 133 := by ring
    _ ≤ q ^ (3 * 63) := Nat.pow_le_pow_right hq (by norm_num)

theorem ggOrdE8_le {q : ℕ} (hq : 1 ≤ q) : ordE8 q ≤ q ^ (3 * 120) := by
  calc ordE8 q ≤ q ^ 120 * q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 *
        q ^ 2 := by
        rw [ordE8]
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 248 := by ring
    _ ≤ q ^ (3 * 120) := pow_le_pow_right₀ hq (by norm_num)

theorem ggTriality_factor_le {q : ℕ} (hq : 2 ≤ q) : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
  have h1 : q ^ 4 + 1 ≤ q ^ (4 + 1) := ggPow_add_one_le hq 4
  have h2 : q ^ (4 + 1) ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc q ^ 8 + q ^ 4 + 1 ≤ q ^ 8 * 2 := by omega
    _ ≤ q ^ 8 * q := Nat.mul_le_mul_left _ hq
    _ = q ^ 9 := by ring

theorem ggOrdTrialityD4_le {q : ℕ} (hq : 2 ≤ q) : ordTrialityD4 q ≤ q ^ (3 * 12) := by
  calc ordTrialityD4 q ≤ q ^ 12 * q ^ 9 * q ^ 6 * q ^ 2 := by
        rw [ordTrialityD4]
        gcongr
        all_goals first | exact Nat.sub_le _ _ | exact ggTriality_factor_le hq
    _ = q ^ 29 := by ring
    _ ≤ q ^ (3 * 12) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem ggOrdSuzuki_le {q : ℕ} (hq : 2 ≤ q) : ordSuzuki q ≤ q ^ (3 * 2) := by
  calc ordSuzuki q ≤ q ^ 2 * q ^ (2 + 1) * q := by
        rw [ordSuzuki]
        gcongr
        all_goals first | exact Nat.sub_le _ _ | exact ggPow_add_one_le hq _
    _ = q ^ (3 * 2) := by ring

theorem ggOrdTwistedF4_le {q : ℕ} (hq : 2 ≤ q) : ordTwistedF4 q ≤ q ^ (3 * 12) := by
  calc ordTwistedF4 q ≤ q ^ 12 * q ^ (6 + 1) * q ^ 4 * q ^ (3 + 1) * q := by
        rw [ordTwistedF4]
        gcongr
        all_goals first | exact Nat.sub_le _ _ | exact ggPow_add_one_le hq _
    _ = q ^ 28 := by ring
    _ ≤ q ^ (3 * 12) := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem ggProfile_bound {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hle : m ≤ 2 ^ (3 * N)) :
    ∃ N r : ℕ, Odd r ∧ m = 2 ^ N * r ∧ m ≤ 2 ^ (3 * N) := by
  obtain ⟨r, hr, hm⟩ := h.two
  exact ⟨N, r, hr, hm, hle⟩

theorem ggCharTwoOrder_bound {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    ∃ N r : ℕ, Odd r ∧ charTwoOrder t n f = 2 ^ N * r ∧ charTwoOrder t n f ≤ 2 ^ (3 * N) := by
  obtain ⟨-, hf, hrest⟩ := hadm
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hq2 : 2 ≤ 2 ^ f := ggTwo_le_two_pow hf
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := hrest
    exact ggProfile_bound (profile_ordA (n := n - 1) (by omega) hf)
      ((ggOrdA_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case PSU =>
    obtain ⟨hn, -⟩ := hrest
    exact ggProfile_bound (profile_ordTwistedA (n := n - 1) (by omega) hf)
      ((ggOrdTwistedA_le hq2 (by omega)).trans_eq (ggTwoPow_three_mul _ _).symm)
  case PSp =>
    exact ggProfile_bound (profile_ordBC (n := n) hf)
      ((ggOrdBC_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    exact ggProfile_bound (profile_ordD (n := n) (by omega) hf)
      ((ggOrdD_le hq1 (by omega)).trans_eq (ggTwoPow_three_mul _ _).symm)
  case POmegaMinus =>
    exact ggProfile_bound (profile_ordTwistedD (n := n) (by omega) hf)
      ((ggOrdTwistedD_le hq2 (by omega)).trans_eq (ggTwoPow_three_mul _ _).symm)
  case G2 =>
    exact ggProfile_bound (profile_ordG2 hf)
      ((ggOrdG2_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case F4 =>
    exact ggProfile_bound (profile_ordF4 hf)
      ((ggOrdF4_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case E6 =>
    exact ggProfile_bound (profile_ordE6 hf)
      ((ggOrdE6_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case E7 =>
    exact ggProfile_bound (profile_ordE7 hf)
      ((ggOrdE7_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case E8 =>
    exact ggProfile_bound (profile_ordE8 hf)
      ((ggOrdE8_le hq1).trans_eq (ggTwoPow_three_mul _ _).symm)
  case twistedE6 =>
    exact ggProfile_bound (profile_ordTwistedE6 hf)
      ((ggOrdTwistedE6_le hq2).trans_eq (ggTwoPow_three_mul _ _).symm)
  case trialityD4 =>
    exact ggProfile_bound (profile_ordTrialityD4 hf)
      ((ggOrdTrialityD4_le hq2).trans_eq (ggTwoPow_three_mul _ _).symm)
  case twistedB2 =>
    exact ggProfile_bound (profile_ordSuzuki hf)
      ((ggOrdSuzuki_le hq2).trans_eq (ggTwoPow_three_mul _ _).symm)
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 =>
    exact ggProfile_bound (profile_ordTwistedF4 hf)
      ((ggOrdTwistedF4_le hq2).trans_eq (ggTwoPow_three_mul _ _).symm)
  case Tits =>
    exact ⟨11, 8775, by decide, ordTits_eq, (by decide : ordTits ≤ 2 ^ (3 * 11))⟩

end CFSG.StandardType
