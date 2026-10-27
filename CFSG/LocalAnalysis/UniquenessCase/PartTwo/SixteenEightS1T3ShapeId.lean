module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OmegaPlusFour
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}

private theorem s16t3_eq_of_two_pow_mul_odd {a b O O' : ℕ} (hO : Odd O) (hO' : Odd O')
    (h : 2 ^ a * O = 2 ^ b * O') : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have h' : 2 ^ a * O = 2 ^ a * (2 ^ (b - a) * O') := by
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
    have hO2 := Nat.eq_of_mul_eq_mul_left (by positivity) h'
    have hdvd : 2 ∣ O := hO2 ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
  · exact hab
  · exfalso
    have h' : 2 ^ b * O' = 2 ^ b * (2 ^ (a - b) * O) := by
      rw [← h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
    have hO2 := Nat.eq_of_mul_eq_mul_left (by positivity) h'
    have hdvd : 2 ∣ O' := hO2 ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    exact (Nat.not_even_iff_odd.mpr hO') (even_iff_two_dvd.mpr hdvd)

private theorem s16t3_odd_pow_sub_one {q k : ℕ} (hq : Even q) (hq1 : 1 ≤ q) (hk : 1 ≤ k) :
    Odd (q ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ hq1) ((Nat.even_pow' (by omega)).mpr hq) odd_one

private theorem s16t3_odd_prod_pow_sub_one {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q)
    (s : Finset ℕ) (e : ℕ → ℕ) (he : ∀ i ∈ s, 1 ≤ e i) :
    Odd (∏ i ∈ s, (q ^ e i - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (s16t3_odd_pow_sub_one hq hq1 (he a (Finset.mem_insert_self a s))).mul
      (ih fun i hi => he i (Finset.mem_insert_of_mem hi))

private theorem s16t3_odd_pow_add_one {q m : ℕ} (hq : Even q) (hm : 1 ≤ m) :
    Odd (q ^ m + 1) :=
  (hq.pow_of_ne_zero (by omega)).add_odd odd_one

private theorem s16t3_card_statedSL_eq_two_pow_mul_odd
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) :
    ∃ O : ℕ, Odd O ∧ Nat.card (StatedSL n K) = 2 ^ (n * (n - 1) / 2) * O := by
  haveI : Fintype K := Fintype.ofFinite K
  by_cases hn : n = 0
  · subst hn
    have hGL : Nat.card (GL (Fin 0) K) = 1 := by
      rw [Matrix.card_GL_field]
      simp
    have hdvd : Nat.card (StatedSL 0 K) ∣ Nat.card (GL (Fin 0) K) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hGL] at hdvd
    exact ⟨1, odd_one, by rw [Nat.dvd_one.mp hdvd]; norm_num⟩
  · have hn1 : 1 ≤ n := by omega
    refine ⟨∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1), ?_, ?_⟩
    · rw [hK]
      exact s16t3_odd_prod_pow_sub_one (q := 2) (by norm_num) (by norm_num) _ _
        (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
    · rw [CFSG.Open.StatedAPI.card_statedSL,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn1, hK]

private theorem s16t3_card_statedSp_eq_two_pow_mul_odd
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (r : ℕ) :
    ∃ O : ℕ, Odd O ∧ Nat.card (StatedSp r K) = 2 ^ (r ^ 2) * O := by
  refine ⟨∏ j ∈ Finset.Icc 1 r, (Nat.card K ^ (2 * j) - 1), ?_, ?_⟩
  · rw [hK]
    exact s16t3_odd_prod_pow_sub_one (q := 2) (by norm_num) (by norm_num) _ _
      (fun j hj => by simp only [Finset.mem_Icc] at hj; omega)
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]

private theorem s16t3_card_omegaPlus_eq_two_pow_mul_odd
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) :
    ∃ O : ℕ, Odd O ∧
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus m K))) =
        2 ^ (m * (m - 1)) * O := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 1) (by simpa using hK)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq : Even (Nat.card K) := by rw [hK]; norm_num
  refine ⟨(Nat.card K ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1),
    (s16t3_odd_pow_sub_one hq hq1 (by omega)).mul
      (s16t3_odd_prod_pow_sub_one hq hq1 _ _ fun i hi => by
        simp only [Finset.mem_Icc] at hi; omega), ?_⟩
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K) hm
  have e1 : ((2 ^ m - 1 : ℕ) : ℤ) = (2 : ℤ) ^ m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    ring
  have e2 : ((∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      ring
  have key : (Nat.card (StatedProj (StatedOmega (StatedQuadPlus m K))) : ℤ) =
      ((2 ^ (m * (m - 1)) * ((Nat.card K ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1)) : ℕ) : ℤ) := by
    rw [h, hK, Nat.cast_mul, Nat.cast_mul, e1, e2]
    push_cast
    ring
  exact_mod_cast key

private theorem s16t3_card_omegaMinus_eq_two_pow_mul_odd
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : 4 ≤ m) :
    ∃ O : ℕ, Odd O ∧
      Nat.card (StatedProj (StatedOmega (StatedQuadMinus m K b c))) =
        2 ^ (m * (m - 1)) * O := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 1) (by simpa using hK)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq : Even (Nat.card K) := by rw [hK]; norm_num
  refine ⟨(Nat.card K ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1),
    (s16t3_odd_pow_add_one hq (by omega)).mul
      (s16t3_odd_prod_pow_sub_one hq hq1 _ _ fun i hi => by
        simp only [Finset.mem_Icc] at hi; omega), ?_⟩
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K) hm
    hirr
  have e1 : ((2 ^ m + 1 : ℕ) : ℤ) = (2 : ℤ) ^ m + 1 := by
    push_cast
    ring
  have e2 : ((∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      ring
  have key : (Nat.card (StatedProj (StatedOmega (StatedQuadMinus m K b c))) : ℤ) =
      ((2 ^ (m * (m - 1)) * ((Nat.card K ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1)) : ℕ) : ℤ) := by
    rw [h, hK, Nat.cast_mul, Nat.cast_mul, e1, e2]
    push_cast
    ring
  exact_mod_cast key

private theorem s16t3_card_statedProj_le_pow {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (H : Subgroup (GL ι K)) :
    Nat.card (StatedProj H) ≤ Nat.card K ^ (Fintype.card ι * Fintype.card ι) := by
  have h1 : Nat.card (StatedProj H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card H ≤ Nat.card (GL ι K) :=
    Nat.card_le_card_of_injective (fun x : H => (x : GL ι K))
      (fun _ _ h => Subtype.ext h)
  have h3 : Nat.card (GL ι K) ≤ Nat.card (Matrix ι ι K) :=
    Nat.card_le_card_of_injective (fun u : GL ι K => (u : Matrix ι ι K))
      (fun _ _ h => Units.ext h)
  have h4 : Nat.card (Matrix ι ι K) =
      Nat.card K ^ (Fintype.card ι * Fintype.card ι) := by
    change Nat.card (ι → ι → K) = Nat.card K ^ (Fintype.card ι * Fintype.card ι)
    rw [Nat.card_fun (α := ι) (β := ι → K), Nat.card_fun (α := ι) (β := K), ← pow_mul]
    congr 1
    rw [Nat.card_eq_fintype_card]
  exact (h1.trans h2).trans (h3.trans (le_of_eq h4))

private theorem s16t3_card_statedProj_dvd_card {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (H : Subgroup (GL ι K)) :
    Nat.card (StatedProj H) ∣ Nat.card H := by
  change Nat.card (↥H ⧸ (StatedScalars ι K).subgroupOf H) ∣ Nat.card ↥H
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars ι K).subgroupOf H)]
  exact ⟨Nat.card ↥((StatedScalars ι K).subgroupOf H), rfl⟩

private theorem s16t3_three_pow_four_not_dvd_card_omegaPlus_small
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : m ≤ 2) :
    ¬ 3 ^ 4 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadPlus m K))) := by
  intro h81
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 1) (by simpa using hK)
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · have hle := s16t3_card_statedProj_le_pow (K := K) (ι := Fin m ⊕ Fin m)
      (StatedOmega (StatedQuadPlus m K))
    have hcard : Nat.card (StatedProj (StatedOmega (StatedQuadPlus m K))) ≤ 16 := by
      refine hle.trans ?_
      rw [hK]
      have hι : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
        simp [Fintype.card_sum]
        omega
      rw [hι]
      have hm2 : 2 * m ≤ 2 := by omega
      have hexp : (2 * m) * (2 * m) ≤ 4 := by nlinarith
      exact Nat.pow_le_pow_right (by norm_num) hexp
    exact Nat.not_dvd_of_pos_of_lt (Nat.card_pos) (by omega) h81
  · have hm2 : m = 2 := by omega
    subst hm2
    have hdvd1 := s16t3_card_statedProj_dvd_card
      (StatedOmega (StatedQuadPlus 2 K))
    have hdvd2 := CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.card_statedOmega_quadPlus_two_dvd
      (K := K)
    have hdvd : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 2 K))) ∣
        2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := hdvd1.trans hdvd2
    rw [hK] at hdvd
    have : 3 ^ 4 ∣ 2 * 2 ^ 2 * (2 ^ 2 - 1) ^ 2 := dvd_trans h81 hdvd
    norm_num at this

private theorem s16t3_three_pow_four_not_dvd_card_omegaMinus_small
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : m ≤ 2) :
    ¬ 3 ^ 4 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadMinus m K b c))) := by
  intro h81
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 1) (by simpa using hK)
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · have hle := s16t3_card_statedProj_le_pow (K := K)
      (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (StatedOmega (StatedQuadMinus m K b c))
    have hcard : Nat.card (StatedProj (StatedOmega (StatedQuadMinus m K b c))) ≤ 16 := by
      refine hle.trans ?_
      rw [hK]
      have hι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 := by
        have hm01 : m = 0 ∨ m = 1 := by omega
        rcases hm01 with rfl | rfl <;> simp [Fintype.card_sum]
      rw [hι]
      norm_num
    exact Nat.not_dvd_of_pos_of_lt (Nat.card_pos) (by omega) h81
  · have hm2 : m = 2 := by omega
    subst hm2
    have hdvd1 := s16t3_card_statedProj_dvd_card
      (StatedOmega (StatedQuadMinus 2 K b c))
    have hcardOmega :=
      CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two (K := K) hirr
    have h60 : Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) = 60 := by
      rw [hcardOmega, hK]
      norm_num [CFSG.SeitzReduction.F4Pilot.ordSL]
    have hdvd : Nat.card (StatedProj (StatedOmega (StatedQuadMinus 2 K b c))) ∣ 60 := by
      rw [h60] at hdvd1
      exact hdvd1
    have : 3 ^ 4 ∣ 60 := dvd_trans h81 hdvd
    norm_num at this

private theorem s16t3_card_omegaPlus_six {X : Type} [Group X] (h : IsOmegaPlus X 6 1) :
    Nat.card X = 20160 := by
  have hAlt : UC22.IsAlt X 8 := s15k_omp6_isAlt8 h
  rw [s15k_six_alt_card hAlt (by norm_num)]
  norm_num [Nat.factorial]

private theorem s16t3_sl_exp_six {n : ℕ} (h : n * (n - 1) / 2 = 15) : n = 6 := by
  have h2 : n * (n - 1) = 30 := by
    have hh := congrArg (fun x => x * 2) h
    rw [Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)] at hh
    norm_num at hh
    exact hh
  have hle : n ≤ 6 := by
    by_contra hlt
    have hn7 : 7 ≤ n := by omega
    have hge : 7 * 6 ≤ n * (n - 1) := Nat.mul_le_mul hn7 (by omega)
    omega
  interval_cases n <;> omega

private theorem s16t3_sl_exp_seven {n : ℕ} (h : n * (n - 1) / 2 = 21) : n = 7 := by
  have h2 : n * (n - 1) = 42 := by
    have hh := congrArg (fun x => x * 2) h
    rw [Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)] at hh
    norm_num at hh
    exact hh
  have hle : n ≤ 7 := by
    by_contra hlt
    have hn8 : 8 ≤ n := by omega
    have hge : 8 * 7 ≤ n * (n - 1) := Nat.mul_le_mul hn8 (by omega)
    omega
  interval_cases n <;> omega

private theorem s16t3_sl_exp_four {n : ℕ} (h : n * (n - 1) / 2 = 6) : n = 4 := by
  have h2 : n * (n - 1) = 12 := by
    have hh := congrArg (fun x => x * 2) h
    rw [Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)] at hh
    norm_num at hh
    exact hh
  have hle : n ≤ 4 := by
    by_contra hlt
    have hn5 : 5 ≤ n := by omega
    have hge : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hn5 (by omega)
    omega
  interval_cases n <;> omega

private theorem s16t3_sq_ne_fifteen {r : ℕ} (h : r ^ 2 = 15) : False := by
  have hle : r ≤ 3 := by
    by_contra hlt
    have hr4 : 4 ≤ r := by omega
    have : 4 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr4 2
    omega
  interval_cases r <;> norm_num at h

private theorem s16t3_sq_ne_twentyOne {r : ℕ} (h : r ^ 2 = 21) : False := by
  have hle : r ≤ 4 := by
    by_contra hlt
    have hr5 : 5 ≤ r := by omega
    have : 5 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr5 2
    omega
  interval_cases r <;> norm_num at h

private theorem s16t3_sq_ne_six {r : ℕ} (h : r ^ 2 = 6) : False := by
  have hle : r ≤ 2 := by
    by_contra hlt
    have hr3 : 3 ≤ r := by omega
    have : 3 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr3 2
    omega
  interval_cases r <;> norm_num at h

private theorem s16t3_mul_pred_ne_fifteen {m : ℕ} (h : m * (m - 1) = 15) : False := by
  have hle : m ≤ 4 := by
    by_contra hlt
    have hm5 : 5 ≤ m := by omega
    have hge : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul hm5 (by omega)
    omega
  interval_cases m <;> norm_num at h

private theorem s16t3_mul_pred_ne_twentyOne {m : ℕ} (h : m * (m - 1) = 21) : False := by
  have hle : m ≤ 5 := by
    by_contra hlt
    have hm6 : 6 ≤ m := by omega
    have hge : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul hm6 (by omega)
    omega
  interval_cases m <;> norm_num at h

private theorem s16t3_mul_pred_eq_six {m : ℕ} (h : m * (m - 1) = 6) : m = 3 := by
  have hle : m ≤ 3 := by
    by_contra hlt
    have hm4 : 4 ≤ m := by omega
    have hge : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm4 (by omega)
    omega
  interval_cases m <;> omega

private theorem s16t3_prime_dvd_factorial_div_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : p ≤ n) : p ∣ n.factorial / 2 := by
  have hn2 : 2 ≤ n := hp.two_le.trans hn
  have h2dvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfact : n.factorial = 2 * (n.factorial / 2) := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel h2dvd).symm
  have hpdvd : p ∣ n.factorial := hp.dvd_factorial.mpr hn
  rw [hfact] at hpdvd
  rcases hp.dvd_mul.mp hpdvd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  · exact h

private theorem s16t3_prime_le_of_dvd_factorial_div_two {p n : ℕ} (hp : p.Prime)
    (hn2 : 2 ≤ n) (h : p ∣ n.factorial / 2) : p ≤ n := by
  have h2dvd : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfact : n.factorial = 2 * (n.factorial / 2) := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel h2dvd).symm
  have hpdvd : p ∣ n.factorial := by
    rw [hfact]
    exact dvd_mul_of_dvd_right h 2
  exact hp.dvd_factorial.mp hpdvd

private theorem s16t3_alt_card_ne {X : Type} [Group X] {n N : ℕ} (h : UC22.IsAlt X n)
    (hcard : Nat.card X = N) (h31 : 31 ∣ N) (h17 : ¬ 17 ∣ N) : False := by
  by_cases hn30 : n ≤ 30
  · have h31not : ¬ 31 ∣ Nat.card X := by
      by_cases hn2 : 2 ≤ n
      · rw [s15k_six_alt_card h hn2]
        intro hdiv
        have hle31 : 31 ≤ n :=
          s16t3_prime_le_of_dvd_factorial_div_two (by norm_num) hn2 hdiv
        omega
      · have hn1 : n ≤ 1 := by omega
        haveI : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
        haveI : Subsingleton (alternatingGroup (Fin n)) :=
          ⟨fun a b => Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _)⟩
        have h1 : Nat.card (alternatingGroup (Fin n)) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
        obtain ⟨e⟩ := h
        rw [Nat.card_congr e.toEquiv, h1]
        norm_num
    exact h31not (hcard ▸ h31)
  · have hn31 : 31 ≤ n := by omega
    have h17dvd : 17 ∣ Nat.card X := by
      rw [s15k_six_alt_card h (by omega)]
      exact s16t3_prime_dvd_factorial_div_two (by norm_num) (by norm_num)
        (by omega : 17 ≤ n)
    exact h17 (hcard ▸ h17dvd)

private theorem s16t3_alt_card_ne_25920 {X : Type} [Group X] {n : ℕ}
    (h : UC22.IsAlt X n) (hcard : Nat.card X = 25920) : False := by
  by_cases hn7 : 7 ≤ n
  · have h7dvd : 7 ∣ Nat.card X := by
      rw [s15k_six_alt_card h (by omega)]
      exact s16t3_prime_dvd_factorial_div_two (by norm_num) (by norm_num) hn7
    rw [hcard] at h7dvd
    norm_num at h7dvd
  · have hn6 : n ≤ 6 := by omega
    by_cases hn2 : 2 ≤ n
    · rw [s15k_six_alt_card h hn2] at hcard
      have hle : n.factorial ≤ 720 := by
        have h := Nat.factorial_le hn6
        norm_num at h ⊢
        exact h
      omega
    · have hn1 : n ≤ 1 := by omega
      haveI : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
      haveI : Subsingleton (alternatingGroup (Fin n)) :=
        ⟨fun a b => Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _)⟩
      have h1 : Nat.card (alternatingGroup (Fin n)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, h1] at hcard
      norm_num at hcard

private theorem s16t3_shape_branch_sl_aux
    (hs : SumOfNatShape L U Z k) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hL : IsSLn ↥L n 1)
    (h81 : 3 ^ 4 ∣ Nat.card ↥L) (hne20160 : Nat.card ↥L ≠ 20160)
    (hne25920 : Nat.card ↥L ≠ 25920) (h31 : 31 ∣ Nat.card ↥L)
    (h17 : ¬ 17 ∣ Nat.card ↥L) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L U Z k := by
  obtain ⟨K, hF, hFin, hK, ⟨eL⟩⟩ := hL
  letI : Field K := hF
  letI : Finite K := hFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨O0, hO0, hcard0⟩ := s16t3_card_statedSL_eq_two_pow_mul_odd (K := K) hK2 n
  have hcardL0 : Nat.card ↥L = Nat.card (StatedSL n K) := Nat.card_congr eL.toEquiv
  obtain ⟨n', h | h | h | h | h⟩ := hs
  · obtain ⟨hSL, hsum⟩ := h
    obtain ⟨K', hF', hFin', hK', ⟨e'⟩⟩ := hSL
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    obtain ⟨O1, hO1, hcard1⟩ := s16t3_card_statedSL_eq_two_pow_mul_odd (K := K') hK'2 n'
    have hcards : Nat.card (StatedSL n K) = Nat.card (StatedSL n' K') := by
      rw [← hcardL0]
      exact Nat.card_congr e'.toEquiv
    have hexp : n * (n - 1) / 2 = n' * (n' - 1) / 2 := by
      apply s16t3_eq_of_two_pow_mul_odd hO0 hO1
      rw [← hcard0, ← hcard1]
      exact hcards
    rcases hn with rfl | rfl
    · have h15 : n' * (n' - 1) / 2 = 15 := by simpa using hexp.symm
      have hn' : n' = 6 := s16t3_sl_exp_six h15
      simpa [hn'] using hsum
    · have h21 : n' * (n' - 1) / 2 = 21 := by simpa using hexp.symm
      have hn' : n' = 7 := s16t3_sl_exp_seven h21
      simpa [hn'] using hsum
  · obtain ⟨hSp, hsum⟩ := h
    obtain ⟨hEven, K', hF', hFin', hK', ⟨e'⟩⟩ := hSp
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    obtain ⟨O1, hO1, hcard1⟩ := s16t3_card_statedSp_eq_two_pow_mul_odd (K := K') hK'2 (n' / 2)
    have hcards : Nat.card (StatedSL n K) = Nat.card (StatedSp (n' / 2) K') := by
      rw [← hcardL0]
      exact Nat.card_congr e'.toEquiv
    have hexp : n * (n - 1) / 2 = (n' / 2) ^ 2 := by
      apply s16t3_eq_of_two_pow_mul_odd hO0 hO1
      rw [← hcard0, ← hcard1]
      exact hcards
    rcases hn with rfl | rfl
    · have h : (n' / 2) ^ 2 = 15 := by simpa using hexp.symm
      exact (s16t3_sq_ne_fifteen h).elim
    · have h : (n' / 2) ^ 2 = 21 := by simpa using hexp.symm
      exact (s16t3_sq_ne_twentyOne h).elim
  · obtain ⟨hOP, hsum⟩ := h
    have hOP' := hOP
    obtain ⟨hEven, K', hF', hFin', hK', ⟨e'⟩⟩ := hOP
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    have hcards : Nat.card (StatedSL n K) =
        Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n' / 2) K'))) := by
      rw [← hcardL0]
      exact Nat.card_congr e'.toEquiv
    by_cases hm4 : 4 ≤ n' / 2
    · obtain ⟨O1, hO1, hcard1⟩ :=
        s16t3_card_omegaPlus_eq_two_pow_mul_odd (K := K') hK'2 hm4
      have hexp : n * (n - 1) / 2 = (n' / 2) * (n' / 2 - 1) := by
        apply s16t3_eq_of_two_pow_mul_odd hO0 hO1
        rw [← hcard0, ← hcard1]
        exact hcards
      rcases hn with rfl | rfl
      · have h : (n' / 2) * (n' / 2 - 1) = 15 := by simpa using hexp.symm
        exact (s16t3_mul_pred_ne_fifteen h).elim
      · have h : (n' / 2) * (n' / 2 - 1) = 21 := by simpa using hexp.symm
        exact (s16t3_mul_pred_ne_twentyOne h).elim
    · have hm3 : n' / 2 ≤ 3 := by omega
      rcases Nat.lt_or_ge (n' / 2) 3 with hm2 | hm3'
      · have h81model : 3 ^ 4 ∣
            Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n' / 2) K'))) := by
          rw [← hcards, ← hcardL0]
          exact h81
        exact (s16t3_three_pow_four_not_dvd_card_omegaPlus_small hK'2 (by omega) h81model).elim
      · have hm : n' / 2 = 3 := by omega
        have hn'6 : n' = 6 := by
          have h2 := Nat.two_mul_div_two_of_even hEven
          omega
        have hOP6 : IsOmegaPlus ↥L 6 1 := by simpa [hn'6] using hOP'
        have hc : Nat.card ↥L = 20160 := s16t3_card_omegaPlus_six hOP6
        exact (hne20160 hc).elim
  · obtain ⟨hOM, hsum⟩ := h
    have hOM' := hOM
    obtain ⟨hEven, K', hF', hFin', b', c', hK', hirr, ⟨e'⟩⟩ := hOM
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    have hcards : Nat.card (StatedSL n K) =
        Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n' / 2) K' b' c'))) := by
      rw [← hcardL0]
      exact Nat.card_congr e'.toEquiv
    by_cases hm4 : 4 ≤ n' / 2
    · obtain ⟨O1, hO1, hcard1⟩ :=
        s16t3_card_omegaMinus_eq_two_pow_mul_odd (K := K') hK'2 hirr hm4
      have hexp : n * (n - 1) / 2 = (n' / 2) * (n' / 2 - 1) := by
        apply s16t3_eq_of_two_pow_mul_odd hO0 hO1
        rw [← hcard0, ← hcard1]
        exact hcards
      rcases hn with rfl | rfl
      · have h : (n' / 2) * (n' / 2 - 1) = 15 := by simpa using hexp.symm
        exact (s16t3_mul_pred_ne_fifteen h).elim
      · have h : (n' / 2) * (n' / 2 - 1) = 21 := by simpa using hexp.symm
        exact (s16t3_mul_pred_ne_twentyOne h).elim
    · have hm3 : n' / 2 ≤ 3 := by omega
      rcases Nat.lt_or_ge (n' / 2) 3 with hm2 | hm3'
      · have h81model : 3 ^ 4 ∣
            Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n' / 2) K' b' c'))) := by
          rw [← hcards, ← hcardL0]
          exact h81
        exact (s16t3_three_pow_four_not_dvd_card_omegaMinus_small hK'2 hirr (by omega)
          h81model).elim
      · have hm : n' / 2 = 3 := by omega
        have hn'6 : n' = 6 := by
          have h2 := Nat.two_mul_div_two_of_even hEven
          omega
        have hOM6 : IsOmegaMinus ↥L 6 1 := by simpa [hn'6] using hOM'
        have hc : Nat.card ↥L = 25920 := (s15k_six_om6 hOM6).1
        exact (hne25920 hc).elim
  · obtain ⟨hAlt, hsum⟩ := h
    have hcards : Nat.card ↥L = Nat.card (alternatingGroup (Fin n')) := by
      obtain ⟨e'⟩ := hAlt
      exact Nat.card_congr e'.toEquiv
    rw [hcards] at h31 h17
    exact (s16t3_alt_card_ne hAlt hcards h31 h17).elim

private theorem s16t3_cardSL_six {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 6 K) = 20158709760 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, Fin.prod_univ_six,
    ← Nat.card_eq_fintype_card, hK]
  rfl

private theorem s16t3_cardSL_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 7 K) = 163849992929280 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, Fin.prod_univ_seven,
    ← Nat.card_eq_fintype_card, hK]
  rfl

private theorem s16t3_shape_branch_omegaMinus_aux
    (hs : SumOfNatShape L U Z k) (hL : IsOmegaMinus ↥L 6 1)
    (hcardL : Nat.card ↥L = 25920) :
    SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) L U Z k := by
  have h81 : 3 ^ 4 ∣ Nat.card ↥L := by rw [hcardL]; norm_num
  obtain ⟨n', h | h | h | h | h⟩ := hs
  · obtain ⟨hSL, hsum⟩ := h
    obtain ⟨K', hF', hFin', hK', ⟨e'⟩⟩ := hSL
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    obtain ⟨O1, hO1, hcard1⟩ := s16t3_card_statedSL_eq_two_pow_mul_odd (K := K') hK'2 n'
    have hcards : Nat.card (StatedSL n' K') = 25920 := by
      rw [← hcardL]
      exact (Nat.card_congr e'.toEquiv).symm
    have hexp : n' * (n' - 1) / 2 = 6 := by
      apply s16t3_eq_of_two_pow_mul_odd hO1 (by norm_num : Odd 405)
      rw [← hcard1]
      norm_num
      exact hcards
    have hn' : n' = 4 := s16t3_sl_exp_four hexp
    have h20160 : Nat.card (StatedSL n' K') = 20160 := by
      rw [hn']
      exact CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK'2
    rw [h20160] at hcards
    norm_num at hcards
  · obtain ⟨hSp, hsum⟩ := h
    obtain ⟨hEven, K', hF', hFin', hK', ⟨e'⟩⟩ := hSp
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    obtain ⟨O1, hO1, hcard1⟩ := s16t3_card_statedSp_eq_two_pow_mul_odd (K := K') hK'2 (n' / 2)
    have hcards : Nat.card (StatedSp (n' / 2) K') = 25920 := by
      rw [← hcardL]
      exact (Nat.card_congr e'.toEquiv).symm
    have hexp : (n' / 2) ^ 2 = 6 := by
      apply s16t3_eq_of_two_pow_mul_odd hO1 (by norm_num : Odd 405)
      rw [← hcard1]
      norm_num
      exact hcards
    exact (s16t3_sq_ne_six hexp).elim
  · obtain ⟨hOP, hsum⟩ := h
    have hOP' := hOP
    obtain ⟨hEven, K', hF', hFin', hK', ⟨e'⟩⟩ := hOP
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    have hcards : Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n' / 2) K'))) = 25920 := by
      rw [← hcardL]
      exact (Nat.card_congr e'.toEquiv).symm
    by_cases hm4 : 4 ≤ n' / 2
    · obtain ⟨O1, hO1, hcard1⟩ :=
        s16t3_card_omegaPlus_eq_two_pow_mul_odd (K := K') hK'2 hm4
      have hexp : (n' / 2) * (n' / 2 - 1) = 6 := by
        apply s16t3_eq_of_two_pow_mul_odd hO1 (by norm_num : Odd 405)
        rw [← hcard1]
        norm_num
        exact hcards
      have hm : n' / 2 = 3 := s16t3_mul_pred_eq_six hexp
      omega
    · have hm3 : n' / 2 ≤ 3 := by omega
      rcases Nat.lt_or_ge (n' / 2) 3 with hm2 | hm3'
      · have h81model : 3 ^ 4 ∣
            Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n' / 2) K'))) := by
          rw [hcards]
          norm_num
        exact (s16t3_three_pow_four_not_dvd_card_omegaPlus_small hK'2 (by omega) h81model).elim
      · have hm : n' / 2 = 3 := by omega
        have hn'6 : n' = 6 := by
          have h2 := Nat.two_mul_div_two_of_even hEven
          omega
        have hOP6 : IsOmegaPlus ↥L 6 1 := by simpa [hn'6] using hOP'
        have hc : Nat.card ↥L = 20160 := s16t3_card_omegaPlus_six hOP6
        rw [hcardL] at hc
        norm_num at hc
  · obtain ⟨hOM, hsum⟩ := h
    have hOM' := hOM
    obtain ⟨hEven, K', hF', hFin', b', c', hK', hirr, ⟨e'⟩⟩ := hOM
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hK'2 : Nat.card K' = 2 := by simpa using hK'
    have hcards : Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n' / 2) K' b' c'))) =
        25920 := by
      rw [← hcardL]
      exact (Nat.card_congr e'.toEquiv).symm
    by_cases hm4 : 4 ≤ n' / 2
    · obtain ⟨O1, hO1, hcard1⟩ :=
        s16t3_card_omegaMinus_eq_two_pow_mul_odd (K := K') hK'2 hirr hm4
      have hexp : (n' / 2) * (n' / 2 - 1) = 6 := by
        apply s16t3_eq_of_two_pow_mul_odd hO1 (by norm_num : Odd 405)
        rw [← hcard1]
        norm_num
        exact hcards
      have hm : n' / 2 = 3 := s16t3_mul_pred_eq_six hexp
      omega
    · have hm3 : n' / 2 ≤ 3 := by omega
      rcases Nat.lt_or_ge (n' / 2) 3 with hm2 | hm3'
      · have h81model : 3 ^ 4 ∣
            Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n' / 2) K' b' c'))) := by
          rw [hcards]
          norm_num
        exact (s16t3_three_pow_four_not_dvd_card_omegaMinus_small hK'2 hirr (by omega)
          h81model).elim
      · have hm : n' / 2 = 3 := by omega
        have hn'6 : n' = 6 := by
          have h2 := Nat.two_mul_div_two_of_even hEven
          omega
        simpa [hn'6] using hsum
  · obtain ⟨hAlt, hsum⟩ := h
    exact (s16t3_alt_card_ne_25920 hAlt hcardL).elim

theorem s16t3_shape_branch_sl (hs : SumOfNatShape L U Z k) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hL : IsSLn ↥L n 1) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L U Z k := by
  rcases hn with rfl | rfl
  · have hL' := hL
    obtain ⟨K, hF, hFin, hK, ⟨eL⟩⟩ := hL
    letI : Field K := hF
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hcardL : Nat.card ↥L = 20158709760 := by
      rw [Nat.card_congr eL.toEquiv]
      exact s16t3_cardSL_six hK2
    exact s16t3_shape_branch_sl_aux hs (Or.inl rfl) hL' (by rw [hcardL]; norm_num)
      (by rw [hcardL]; norm_num) (by rw [hcardL]; norm_num) (by rw [hcardL]; norm_num)
      (by rw [hcardL]; norm_num)
  · have hL' := hL
    obtain ⟨K, hF, hFin, hK, ⟨eL⟩⟩ := hL
    letI : Field K := hF
    letI : Finite K := hFin
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hcardL : Nat.card ↥L = 163849992929280 := by
      rw [Nat.card_congr eL.toEquiv]
      exact s16t3_cardSL_seven hK2
    exact s16t3_shape_branch_sl_aux hs (Or.inr rfl) hL' (by rw [hcardL]; norm_num)
      (by rw [hcardL]; norm_num) (by rw [hcardL]; norm_num) (by rw [hcardL]; norm_num)
      (by rw [hcardL]; norm_num)

theorem s16t3_shape_branch_omegaMinus (hs : SumOfNatShape L U Z k) (hL : IsOmegaMinus ↥L 6 1) :
    SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) L U Z k := by
  have hcardL : Nat.card ↥L = 25920 := (s15k_six_om6 hL).1
  exact s16t3_shape_branch_omegaMinus_aux hs hL hcardL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
