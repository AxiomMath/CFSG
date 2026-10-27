module

public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.B69Num
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Background.F918Z4c1Sz

public section

namespace CFSG.Quasithin.H13.L828N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2

@[expose] def E22Simple (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n X ∨ IsSz n X)) ∨
  (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 X) ∨
  (∃ n : ℕ, IsBenderOf n X) ∨
  (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n X ∨ IsSp4Prime n X)) ∨
  (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
    IsPSL 2 p e X) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ((p % 4 = 1 ∧ IsPSU 3 p 1 X) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 X)))

private theorem gcd_three_cases_828N (m : ℕ) :
    (3 ∣ m ∧ Nat.gcd 3 m = 3) ∨ (¬ 3 ∣ m ∧ Nat.gcd 3 m = 1) := by
  by_cases h : 3 ∣ m
  · exact Or.inl ⟨h, Nat.gcd_eq_left h⟩
  · exact Or.inr ⟨h, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h⟩

private theorem three_dvd_of_mul_gcd_828N {c m N : ℕ} (hc : c * Nat.gcd 3 m = N)
    (h3 : 3 ∣ N) (h9 : 3 ∣ m → 9 ∣ N) : 3 ∣ c := by
  rcases gcd_three_cases_828N m with ⟨hm, hg⟩ | ⟨-, hg⟩
  · rw [hg] at hc
    have := h9 hm
    omega
  · rw [hg] at hc
    omega

private theorem two_dvd_of_mul_gcd_828N {c m N : ℕ} (hc : c * Nat.gcd 3 m = N)
    (h2 : 2 ∣ N) : 2 ∣ c := by
  rcases gcd_three_cases_828N m with ⟨-, hg⟩ | ⟨-, hg⟩ <;> rw [hg] at hc <;> omega

private theorem three_dvd_sq_sub_one_828N {q : ℕ} (h : q % 3 ≠ 0) : 3 ∣ q ^ 2 - 1 := by
  have h2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have hr : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases hr with hr | hr <;> simp [hr]
  generalize q ^ 2 = r at h2 ⊢
  omega

private theorem three_dvd_cube_sub_one_828N {q : ℕ} (h : q % 3 = 1) : 3 ∣ q ^ 3 - 1 := by
  have h3 : q ^ 3 % 3 = 1 := by simp [Nat.pow_mod, h]
  generalize q ^ 3 = r at h3 ⊢
  omega

private theorem three_dvd_cube_add_one_828N {q : ℕ} (h : q % 3 = 2) : 3 ∣ q ^ 3 + 1 := by
  have h3 : q ^ 3 % 3 = 2 := by simp [Nat.pow_mod, h]
  generalize q ^ 3 = r at h3 ⊢
  omega

private theorem two_pow_mod_three_ne_zero_828N (n : ℕ) : 2 ^ n % 3 ≠ 0 := by
  intro h
  have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

private theorem two_dvd_cube_mul_sq_sub_one_828N (q k : ℕ) :
    2 ∣ q ^ 3 * ((q ^ 2 - 1) * k) := by
  rcases Nat.even_or_odd q with he | ho
  · exact Dvd.dvd.mul_right (dvd_pow (even_iff_two_dvd.mp he) (by norm_num)) _
  · have hq : q % 2 = 1 := Nat.odd_iff.mp ho
    have hsq : q ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hq]
    have h2 : 2 ∣ q ^ 2 - 1 := by
      generalize q ^ 2 = r at hsq ⊢
      omega
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h2 k) _

private theorem three_dvd_psl3_828N {q c : ℕ} (hq : 0 < q)
    (hc : c * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) : 3 ∣ c := by
  refine three_dvd_of_mul_gcd_828N hc ?_ ?_
  · by_cases h0 : q % 3 = 0
    · exact Dvd.dvd.mul_right (dvd_pow (Nat.dvd_of_mod_eq_zero h0) (by norm_num)) _
    · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one_828N h0) _) _
  · intro h9
    have hr : q % 3 = 1 := by omega
    have hA : 3 ∣ q ^ 2 - 1 := three_dvd_sq_sub_one_828N (by omega)
    have hB : 3 ∣ q ^ 3 - 1 := three_dvd_cube_sub_one_828N hr
    exact Dvd.dvd.mul_left (Nat.mul_dvd_mul hA hB) _

private theorem three_dvd_psu3_828N {q c : ℕ}
    (hc : c * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) : 3 ∣ c := by
  refine three_dvd_of_mul_gcd_828N hc ?_ ?_
  · by_cases h0 : q % 3 = 0
    · exact Dvd.dvd.mul_right (dvd_pow (Nat.dvd_of_mod_eq_zero h0) (by norm_num)) _
    · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one_828N h0) _) _
  · intro h9
    have hr : q % 3 = 2 := by omega
    have hA : 3 ∣ q ^ 2 - 1 := three_dvd_sq_sub_one_828N (by omega)
    have hB : 3 ∣ q ^ 3 + 1 := three_dvd_cube_add_one_828N hr
    exact Dvd.dvd.mul_left (Nat.mul_dvd_mul hA hB) _

private theorem two_three_dvd_of_psl3_828N {X : Type} [Group X] {q : ℕ} (hq : 0 < q)
    (hc : Nat.card X * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :
    2 ∣ Nat.card X ∧ 3 ∣ Nat.card X :=
  ⟨two_dvd_of_mul_gcd_828N hc (two_dvd_cube_mul_sq_sub_one_828N q _),
    three_dvd_psl3_828N hq hc⟩

private theorem two_three_dvd_of_psu3_828N {X : Type} [Group X] {q : ℕ}
    (hc : Nat.card X * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :
    2 ∣ Nat.card X ∧ 3 ∣ Nat.card X :=
  ⟨two_dvd_of_mul_gcd_828N hc (two_dvd_cube_mul_sq_sub_one_828N q _),
    three_dvd_psu3_828N hc⟩

private theorem two_three_dvd_psl3_two_828N {X : Type} [Group X] {n : ℕ}
    (h : IsPSL 3 2 n X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X :=
  two_three_dvd_of_psl3_828N (q := 2 ^ n) (by positivity)
    (CFSG.Quasithin.B69.card_psl_three_mul h)

private theorem two_three_dvd_psl3_prime_828N {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (h : IsPSL 3 p 1 X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  have hc := CFSG.Quasithin.B69.card_psl_three_mul h
  rw [pow_one] at hc
  exact two_three_dvd_of_psl3_828N hp.pos hc

private theorem two_three_dvd_psu3_two_828N {X : Type} [Group X] {n : ℕ}
    (h : IsPSU 3 2 n X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X :=
  two_three_dvd_of_psu3_828N (q := 2 ^ n) (CFSG.Quasithin.B69.card_psu_three_mul h)

private theorem two_three_dvd_psu3_prime_828N {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (h : IsPSU 3 p 1 X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  have hc := CFSG.Quasithin.B69.card_psu_three_mul h
  rw [pow_one] at hc
  exact two_three_dvd_of_psu3_828N hc

private theorem two_three_dvd_psp4_828N {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : IsPSp4 2 n X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  rw [CFSG.Quasithin.B69.card_psp_four h]
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  refine ⟨Dvd.dvd.mul_right (dvd_pow h2 (by norm_num)) _, ?_⟩
  exact Dvd.dvd.mul_left
    (Dvd.dvd.mul_right (three_dvd_sq_sub_one_828N (two_pow_mod_three_ne_zero_828N n)) _) _

private theorem two_three_dvd_alt_six_828N {X : Type} [Group X] (h : IsAlt 6 X) :
    2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have hc : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  rw [hc]
  exact ⟨by norm_num, by norm_num⟩

private theorem two_three_dvd_psl22_828N {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 2 2 n X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  refine ⟨?_, CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two h⟩
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two h]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

private theorem two_three_dvd_psl2_odd_828N {X : Type} [Group X] {p e : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (he : e = 1 ∨ e = 2) (hq8 : p ^ e % 8 = 1 ∨ p ^ e % 8 = 7)
    (h : IsPSL 2 p e X) : 2 ∣ Nat.card X ∧ 3 ∣ Nat.card X := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases he with rfl | rfl <;> norm_num at hq8
  have hc := CFSG.Open.StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd hp hp2 h
  have hq3 : p ^ e % 3 ≠ 0 := by
    intro h0
    have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
  have h4 : 4 ∣ p ^ e * ((p ^ e) ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have hsq : (p ^ e) ^ 2 % 8 = 1 := by
      rw [Nat.pow_mod]
      rcases hq8 with h8 | h8 <;> simp [h8]
    generalize (p ^ e) ^ 2 = r at hsq ⊢
    omega
  have h3 : 3 ∣ p ^ e * ((p ^ e) ^ 2 - 1) :=
    Dvd.dvd.mul_left (three_dvd_sq_sub_one_828N hq3) _
  generalize p ^ e * ((p ^ e) ^ 2 - 1) = N at hc h4 h3
  constructor <;> omega

private theorem odd_of_isSz_828N {X : Type} [Group X] {n : ℕ} (h : IsSz n X) : Odd n := by
  obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := h
  exact ⟨a, hf⟩

private theorem four_dvd_card_isSz_828N {X : Type} [Group X] {n : ℕ} (h : IsSz n X) :
    4 ∣ Nat.card X := by
  obtain ⟨m, hm⟩ := odd_of_isSz_828N h
  have hn0 : n ≠ 0 := by omega
  rw [CFSG.Quasithin.card_of_isSz h]
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
  have h4 : 4 ∣ (2 ^ n) ^ 2 := by
    rw [sq]
    exact Nat.mul_dvd_mul h2 h2
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h4 _) _

private theorem e22Simple_dvd_828N {X : Type} [Group X] (h : E22Simple X) :
    (∃ n : ℕ, Odd n ∧ IsSz n X ∧ 4 ∣ Nat.card X) ∨ (2 ∣ Nat.card X ∧ 3 ∣ Nat.card X) := by
  rcases h with h | h | h | h | h | h
  · obtain ⟨n, hn, h1⟩ := h
    rcases h1 with h1 | h1
    · exact Or.inr (two_three_dvd_psl22_828N hn h1)
    · exact Or.inl ⟨n, odd_of_isSz_828N h1, h1, four_dvd_card_isSz_828N h1⟩
  · obtain ⟨p, hp, hp8, h1⟩ := h
    have hp3 : p ≠ 3 := by
      rintro rfl
      norm_num at hp8
    have hq8 : p ^ 1 % 8 = 1 ∨ p ^ 1 % 8 = 7 := by
      rw [pow_one]
      exact hp8
    exact Or.inr (two_three_dvd_psl2_odd_828N (e := 1) hp hp3 (Or.inl rfl) hq8 h1)
  · obtain ⟨n, hB⟩ := h
    obtain ⟨hn2, h1 | h1 | h1⟩ := hB
    · exact Or.inr (two_three_dvd_psl22_828N hn2 h1)
    · exact Or.inl ⟨n, odd_of_isSz_828N h1, h1, four_dvd_card_isSz_828N h1⟩
    · exact Or.inr (two_three_dvd_psu3_two_828N h1)
  · obtain ⟨n, hn, h1⟩ := h
    rcases h1 with h1 | h1
    · exact Or.inr (two_three_dvd_psl3_two_828N h1)
    · unfold E2.IsSp4Prime at h1
      split_ifs at h1 with hn1
      · exact Or.inr (two_three_dvd_alt_six_828N h1)
      · exact Or.inr (two_three_dvd_psp4_828N hn h1)
  · obtain ⟨p, e, hp, hp3, he, hq8, h1⟩ := h
    exact Or.inr (two_three_dvd_psl2_odd_828N hp (by omega) he hq8 h1)
  · obtain ⟨p, hp, -, h1⟩ := h
    rcases h1 with h1 | h1
    · exact Or.inr (two_three_dvd_psu3_prime_828N hp h1.2)
    · exact Or.inr (two_three_dvd_psl3_prime_828N hp h1.2)

private theorem isSimpleGroup_of_isSp4Prime_828N {X : Type} [Group X] {n : ℕ}
    (h : E2.IsSp4Prime n X) : IsSimpleGroup X := by
  unfold E2.IsSp4Prime at h
  split_ifs at h with hn
  · obtain ⟨e⟩ := h
    exact (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 2 n h

private theorem e22Simple_isSimple_828N {X : Type} [Group X] (h : E22Simple X) :
    IsSimpleGroup X := by
  rcases h with h | h | h | h | h | h
  · obtain ⟨n, -, h1⟩ := h
    rcases h1 with h1 | h1
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h1).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n h1).2
  · obtain ⟨p, -, -, h1⟩ := h
    exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 h1).2
  · obtain ⟨n, hB⟩ := h
    obtain ⟨-, h1 | h1 | h1⟩ := hB
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 2 n h1).2
    · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n h1).2
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 2 n h1).2
  · obtain ⟨n, -, h1⟩ := h
    rcases h1 with h1 | h1
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 n h1).2
    · exact isSimpleGroup_of_isSp4Prime_828N h1
  · obtain ⟨p, e, -, -, -, -, h1⟩ := h
    exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p e h1).2
  · obtain ⟨p, -, -, h1⟩ := h
    rcases h1 with h1 | h1
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p 1 h1.2).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 p 1 h1.2).2

private theorem not_prime_of_two_three_dvd_828N {c : ℕ} (h2 : 2 ∣ c) (h3 : 3 ∣ c) :
    ¬ c.Prime := by
  intro hp
  have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  subst h
  norm_num at h3

private theorem not_prime_of_four_dvd_828N {c : ℕ} (h4 : 4 ∣ c) : ¬ c.Prime := by
  intro hp
  have h2 : 2 ∣ c := (by norm_num : (2 : ℕ) ∣ 4).trans h4
  have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  subst h
  norm_num at h4

private theorem nonabelian_of_simple_not_prime_828N {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  letI : IsMulCommutative X := ⟨⟨fun a b => hc a b⟩⟩
  exact hp (Group.is_simple_iff_prime_card.mp hs)

theorem e22Simple_of_cases {Γ : Type} [Group Γ] {H T M K : Subgroup Γ}
    (h : E22CasesNoN H T M K) : E22Simple ↥(star M H K) := by
  unfold E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨-, t, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, hn, h1, -⟩ | ⟨p, hp, hp8, h1, -, -⟩
    · rcases h1 with h1 | h1
      · exact Or.inl ⟨n, hn, Or.inl h1⟩
      · exact Or.inl ⟨n, hn, Or.inr h1⟩
    · exact Or.inr (Or.inl ⟨p, hp, hp8, h1⟩)
  · rcases h2 with ⟨n, hB, -⟩ | ⟨n, hn, h2, -, -⟩ | ⟨p, e, hp, hp3, he, hq8, h2, -⟩ |
        ⟨p, hp, hp2, h2, -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨n, hB⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hq8, h2⟩))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, ?_⟩))))
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h2.1, h2.2.1⟩

theorem e22Simple_simple {X : Type} [Group X] (h : E22Simple X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := e22Simple_isSimple_828N h
  refine ⟨hs, nonabelian_of_simple_not_prime_828N hs ?_⟩
  rcases e22Simple_dvd_828N h with ⟨n, -, -, h4⟩ | ⟨h2, h3⟩
  · exact not_prime_of_four_dvd_828N h4
  · exact not_prime_of_two_three_dvd_828N h2 h3

@[expose] def SzCasesE22 {Γ : Type} [Group Γ] (H T M K : Subgroup Γ) : Prop :=
  (kerIn M H = pCoreOf 2 H ∧
      (∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) ∧
      ∃ n : ℕ, Odd n ∧ IsSz n ↥(star M H K)) ∨
    (T ≤ Subgroup.normalizer (K : Set Γ) ∧
      (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
        ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
      ∃ n : ℕ, Odd n ∧ IsSz n ↥(star M H K))

theorem e22Cases_Sz {Γ : Type} [Group Γ] {H T M K : Subgroup Γ} (h : E22CasesNoN H T M K)
    (h3 : ¬ 3 ∣ Nat.card ↥(star M H K)) : SzCasesE22 H T M K := by
  unfold SzCasesE22
  unfold E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTN, hJ2, h2⟩
  · left
    refine ⟨hJ, ⟨t, ht, hne, hM⟩, ?_⟩
    rcases h1 with ⟨n, hn, h1, -⟩ | ⟨p, hp, hp8, h1, -, -⟩
    · rcases h1 with h1 | h1
      · exact absurd (two_three_dvd_psl22_828N hn h1).2 h3
      · exact ⟨n, odd_of_isSz_828N h1, h1⟩
    · have hp3 : p ≠ 3 := by
        rintro rfl
        norm_num at hp8
      have hq8 : p ^ 1 % 8 = 1 ∨ p ^ 1 % 8 = 7 := by
        rw [pow_one]
        exact hp8
      exact absurd (two_three_dvd_psl2_odd_828N (e := 1) hp hp3 (Or.inl rfl) hq8 h1).2 h3
  · right
    refine ⟨hTN, hJ2, ?_⟩
    rcases h2 with ⟨n, hB, -⟩ | ⟨n, hn, h2, -, -⟩ | ⟨p, e, hp, hp3, he, hq8, h2, -⟩ |
        ⟨p, hp, hp2, h2, -⟩
    · obtain ⟨hn2, h1 | h1 | h1⟩ := hB
      · exact absurd (two_three_dvd_psl22_828N hn2 h1).2 h3
      · exact ⟨n, odd_of_isSz_828N h1, h1⟩
      · exact absurd (two_three_dvd_psu3_two_828N h1).2 h3
    · exfalso
      rcases h2 with h1 | h1
      · exact h3 (two_three_dvd_psl3_two_828N h1).2
      · unfold E2.IsSp4Prime at h1
        split_ifs at h1 with hn1
        · exact h3 (two_three_dvd_alt_six_828N h1).2
        · exact h3 (two_three_dvd_psp4_828N hn h1).2
    · exact absurd (two_three_dvd_psl2_odd_828N hp (by omega) he hq8 h2).2 h3
    · exfalso
      rcases h2 with h1 | h1
      · exact h3 (two_three_dvd_psu3_prime_828N hp h1.2).2
      · exact h3 (two_three_dvd_psl3_prime_828N hp h1.2.1).2

end CFSG.Quasithin.H13.L828N
