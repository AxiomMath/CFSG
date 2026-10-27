module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Vol2.Ch1EightFourList

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Ch1Four

theorem exists_odd_of_mul_eq {m d a P : ℕ} (hm : m ≠ 0) (hd : Odd d) (hP : Odd P)
    (h : m * d = 2 ^ a * P) : ∃ o, Odd o ∧ m = 2 ^ a * o := by
  obtain ⟨b, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have e : 2 ^ b * (o * d) = 2 ^ a * P := by rw [← h]; ring
  obtain ⟨hab, -⟩ := two_pow_mul_odd_inj (ho.mul hd) hP e
  exact ⟨o, ho, by rw [hab]⟩

theorem card_G12_of_isYAmalgam {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y]
    {T : Subgroup Y} (h : IsYAmalgam α T) {a o : ℕ} (ho : Odd o) (hY : Nat.card Y = 2 ^ a * o) :
    ∃ o', Odd o' ∧ Nat.card α.G12 = 2 ^ a * o' := by
  obtain ⟨M₁, M₂, hpair, ⟨φ⟩⟩ := h
  obtain ⟨hT, -, hM⟩ := hpair
  have hT1 : Subgroup.normalizer (T : Set Y) ≤ M₁ := ((hM M₁).mpr (Or.inl rfl)).2
  have hT2 : Subgroup.normalizer (T : Set Y) ≤ M₂ := ((hM M₂).mpr (Or.inr rfl)).2
  have hTM : T ≤ M₁ ⊓ M₂ := le_inf (Subgroup.le_normalizer.trans hT1)
    (Subgroup.le_normalizer.trans hT2)
  have hcard : Nat.card α.G12 = Nat.card ↥(M₁ ⊓ M₂) := Nat.card_congr φ.φ12.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := hT.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ T.index := by
    have : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hY' : Nat.card Y = 2 ^ b * T.index := by rw [← hb, Subgroup.card_mul_index]
  have hba : b = a := (two_pow_mul_odd_inj (Nat.odd_iff.mpr (by omega)) ho (hY'.symm.trans hY)).1
  have hrel : Nat.card ↥(M₁ ⊓ M₂) = 2 ^ b * T.relIndex (M₁ ⊓ M₂) := by
    rw [← hb, ← Subgroup.relIndex_mul_card (H := T) (K := M₁ ⊓ M₂), inf_eq_left.mpr hTM, mul_comm]
  have hodd : Odd (T.relIndex (M₁ ⊓ M₂)) := by
    refine Nat.odd_iff.mpr ?_
    have hdvd : T.relIndex (M₁ ⊓ M₂) ∣ T.index := Subgroup.relIndex_dvd_index_of_le hTM
    by_contra hev
    exact hidx ((Nat.dvd_of_mod_eq_zero (by omega)).trans hdvd)
  exact ⟨_, hodd, by rw [hcard, hrel, hba]⟩

section Orders

variable {Y : Type} [Group Y]

theorem card_psl3_two_part {n : ℕ} (h : LieModel Y .PSL 3 2 n) :
    Finite Y ∧ ∃ o, Odd o ∧ Nat.card Y = 2 ^ (3 * n) * o := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hfin := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hc
    refine ⟨hfin, ?_⟩
    obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have hm := card_psl3_mul (K := K)
    rw [hK, ← Nat.card_congr e.toEquiv] at hm
    have hq : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
    have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hP : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      (odd_pow_sub_one_of_even hq hq1 (by norm_num)).mul
        (odd_pow_sub_one_of_even hq hq1 (by norm_num))
    have hd : Odd (Nat.gcd 3 (2 ^ n - 1)) :=
      Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
    have hm0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    exact exists_odd_of_mul_eq hm0 hd hP (by rw [hm, ← pow_mul, mul_comm n 3])
  all_goals exact absurd h0 (by norm_num)

theorem card_psp4_two_part {n : ℕ} (h : LieModel Y .PSp 2 2 n) :
    Finite Y ∧ ∃ o, Odd o ∧ Nat.card Y = 2 ^ (4 * n) * o := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hfin := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hc
    refine ⟨hfin, ?_⟩
    obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    have hm := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := K) 2
    rw [hK, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num),
      ← Nat.card_congr e.toEquiv] at hm
    have hq : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
    have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hP : Odd (((2 ^ n) ^ (2 * 1) - 1) * ((2 ^ n) ^ (2 * 2) - 1)) :=
      (odd_pow_sub_one_of_even hq hq1 (by norm_num)).mul
        (odd_pow_sub_one_of_even hq hq1 (by norm_num))
    have hm0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    exact exists_odd_of_mul_eq hm0 odd_one hP
      (by rw [mul_one, hm, ← pow_mul, show n * 2 ^ 2 = 4 * n by ring])
  all_goals exact absurd h0 (by norm_num)

theorem toNat_four_sub_neg_one {q : ℕ} (hq : 1 ≤ q) :
    (((q : ℤ) ^ 4 - (-1) ^ 4).toNat) = q ^ 4 - 1 := by
  have : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  rw [show ((-1 : ℤ)) ^ 4 = 1 by norm_num, show ((q : ℤ) ^ 4 - 1) = ((q ^ 4 - 1 : ℕ) : ℤ) by
    push_cast [this]; ring, Int.toNat_natCast]

theorem card_psu4_two_part {m : ℕ} (h : LieModel Y .PSU 4 2 m) :
    Finite Y ∧ ∃ o, Odd o ∧ Nat.card Y = 2 ^ (6 * m) * o := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hfin := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hc
    refine ⟨hfin, ?_⟩
    obtain ⟨⟨-, hm1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hq : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
    have hg : Nat.gcd 4 (2 ^ m + 1) = 1 :=
      CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one (by simpa using
        CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one hm1 (n := 1) le_rfl)
    have hm := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hm1 hK
      (n := 4) (by norm_num)
    rw [show 4 * (4 - 1) / 2 = 6 from rfl, show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide,
      Finset.prod_insert (by decide), Finset.prod_pair (by norm_num), toNat_sq_sub_neg_one hq1,
      toNat_cube_sub_neg_one, toNat_four_sub_neg_one hq1, hg, Nat.div_one,
      ← Nat.card_congr e.toEquiv] at hm
    have hP : Odd (((2 ^ m) ^ 2 - 1) * (((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 4 - 1))) :=
      (odd_pow_sub_one_of_even hq hq1 (by norm_num)).mul
        ((odd_pow_add_one_of_even hq (by norm_num)).mul
          (odd_pow_sub_one_of_even hq hq1 (by norm_num)))
    have hm0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    exact exists_odd_of_mul_eq hm0 odd_one hP (by rw [mul_one, hm, ← pow_mul, mul_comm m])
  all_goals exact absurd h0 (by norm_num)

end Orders

theorem not_isU4ExtTwo {α : RankTwoAmalgam.{0}} {n m : ℕ} (hnm : n = 2 * m)
    (hα : IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 n) ∨
      IsAmalgamOfGroup α (IsLieOverTwo .PSp 2 n)) :
    ¬ IsU4ExtTwo m α := by
  rintro ⟨Y', _, Yh, _, ι, hY', hinj, hidx, T', hT'⟩
  obtain ⟨hfin', o', ho', hc'⟩ := card_psu4_two_part hY'
  have hYh : Nat.card Yh = 2 ^ (6 * m + 1) * o' := by
    have h1 := Subgroup.card_mul_index ι.range
    rw [hidx, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hc'] at h1
    rw [← h1, pow_succ]
    ring
  have : Finite Yh :=
    Nat.finite_of_card_ne_zero (by rw [hYh]; exact mul_ne_zero (by positivity) ho'.pos.ne')
  obtain ⟨o₁, ho₁, h₁⟩ := card_G12_of_isYAmalgam hT' ho' hYh
  rcases hα with ⟨Y, _, hY, T, hT⟩ | ⟨Y, _, hY, T, hT⟩
  · obtain ⟨hfin, o, ho, hc⟩ := card_psl3_two_part hY
    have := hfin
    obtain ⟨o₂, ho₂, h₂⟩ := card_G12_of_isYAmalgam hT ho hc
    have := (two_pow_mul_odd_inj ho₂ ho₁ (h₂.symm.trans h₁)).1
    omega
  · obtain ⟨hfin, o, ho, hc⟩ := card_psp4_two_part hY
    have := hfin
    obtain ⟨o₂, ho₂, h₂⟩ := card_G12_of_isYAmalgam hT ho hc
    have := (two_pow_mul_odd_inj ho₂ ho₁ (h₂.symm.trans h₁)).1
    omega

theorem alt_a_of_amalgam (h526 : Stmt5_2_6) {G : Type} [Group G] [Finite G]
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hα : IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSL 3 n) ∨
      IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSp 2 n)) :
    L₂ = oTwoUpper H ∧ sec52S M H ≤ L ∧ sec52S M H ≤ oTwoUpper H ∧
      pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H) ∧
      sec52AlphaPrime M L H B D = sec52Alpha M L H B D L₂ := by
  obtain ⟨-, hL₂K, -, -, -, -, hKT, halt⟩ := h526 G T M L V H B D L₂ n hyp
  rcases halt with ⟨hSL, hSK, -, hKS⟩ | ⟨m, hnm, -, hU4, -⟩
  · refine ⟨hL₂K, hSL, hSK, hKT.trans hKS, ?_⟩
    simp only [sec52AlphaPrime, sec52Alpha, sec52G1, sec52G2, inf_eq_left.mpr hSL, hL₂K]
  · exact absurd hU4 (not_isU4ExtTwo hnm hα)

end CFSG.Quasithin.H13
