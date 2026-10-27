module

public import CFSG.RankThree.PartOne.BRANCH.Defs
public import CFSG.RankThree.PartOne.BRANCH.RankFinite
public import CFSG.RankThree.PartOne.Q1327C.BNoCube

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.N143X

@[expose] def NoSevenCube (q : ℕ) (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup X, CFSG.IsElementaryAbelian q E → Nat.card E = q ^ 7 → False

@[expose] def G2ThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), ChevalleyExceptionalModel X .G2 2 f → NoSevenCube 3 X

@[expose] def TrialityThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ),
    ChevalleyExceptionalModel X .trialityD4 2 f → NoSevenCube 3 X

@[expose] def ReeThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), ReeTitsModel X .twistedF4 2 f → NoSevenCube 3 X

theorem exists_sub_card_pow_three {X : Type} [Group X] {q : ℕ} (hq : q.Prime) {D : Subgroup X}
    (hD : CFSG.IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 7) :
    ∃ E : Subgroup X, (∀ x ∈ E, x ^ q = 1) ∧ Nat.card E = q ^ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 7 hq.ne_zero)
  have hdvd : q ^ 3 ∣ Nat.card D := by
    rw [hcard]
    exact pow_dvd_pow q (by norm_num)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  refine ⟨H.map D.subtype, ?_, ?_⟩
  · rintro _ ⟨d, -, rfl⟩
    exact elemPow_eq_one_of_isElementaryAbelian (p := q) (d : X) d.2
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hH]

theorem false_G2_five
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .G2 2 f)
    {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 5 = 1) (hcard : Nat.card E = 5 ^ 3) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hmod
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : X ≃* adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
  have hp : Nat.Prime 5 := by norm_num
  have hpq : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  refine Q1327C.false_of_pow_three_G2_five K hp le_rfl hpq
    (E := E.map (e : X →* adjointGroup .G2 K)) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    change (e x) ^ 5 = 1
    rw [← map_pow, hE x hx, map_one]
  · rw [← Nat.card_congr (e.subgroupMap E).toEquiv]
    exact hcard

theorem evenLieSevenRank_of_exc3
    (hG2 : G2ThreeRank) (hTri : TrialityThreeRank) (hRee : ReeThreeRank) :
    EvenLieSevenRank := by
  intro X _ _ hs hnonab hEven q hq35 D hD hcard
  have hq : q.Prime := by rcases hq35 with rfl | rfl <;> norm_num
  obtain ⟨t, n, f, hadm, hLie, hsmall⟩ := hEven
  rcases hLie with ⟨ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, rfl, hmod⟩
  ·
    cases t
    case PSL =>
      by_cases h5 : n ≤ 5
      · exact false_psl h5 hmod hq hq35 hD hcard
      · obtain ⟨hn67, hf1⟩ : (n = 6 ∨ n = 7) ∧ f = 1 := by
          rcases hsmall with h | h
          · exact absurd h h5
          · exact h
        subst hf1
        exact false_psl_two hn67 hmod hq35 hcard
    case PSU =>
      by_cases h5 : n ≤ 5
      · exact false_psu h5 hmod hq hq35 hD hcard
      · obtain ⟨hn6, hf1⟩ : n = 6 ∧ f = 1 := by
          rcases hsmall with h | h
          · exact absurd h h5
          · exact h
        subst hn6
        subst hf1
        exact false_psu_six_two hmod hq35 hcard
    case PSp =>
      by_cases h4 : n ≤ 4
      · exact false_psp h4 hmod hq hq35 hD hcard
      · exact absurd hsmall h4
    case POmegaOdd => exact absurd rfl hmod.1.2.2.2
    case POmegaPlus =>
      by_cases h4 : n ≤ 4
      · exact false_pomegaPlus h4 hmod hq hq35 hD hcard
      · exact absurd hsmall h4
    case POmegaMinus =>
      by_cases h4 : n ≤ 4
      · exact false_pomegaMinus h4 hmod hq hq35 hD hcard
      · exact absurd hsmall h4
    all_goals exact hmod.2.elim
  ·
    cases t
    case G2 =>
      rcases hq35 with rfl | rfl
      · exact hG2 X f hmod D hD hcard
      · obtain ⟨E, hE, hEcard⟩ := exists_sub_card_pow_three Nat.prime_five hD hcard
        exact false_G2_five hmod hE hEcard
    case trialityD4 =>
      rcases hq35 with rfl | rfl
      · exact hTri X f hmod D hD hcard
      · obtain ⟨E, hE, hEcard⟩ := exists_sub_card_pow_three Nat.prime_five hD hcard
        exact Q1327C.false_of_pow_three_triality_five hmod Nat.prime_five le_rfl hE hEcard
    case F4 =>
      have hf1 : f = 1 := hsmall
      subst hf1
      exact false_F4_two (by simpa using hmod.2) hq35 hcard
    case E6 => exact hsmall.elim
    case E7 => exact hsmall.elim
    case E8 => exact hsmall.elim
    case twistedE6 => exact hsmall.elim
    all_goals exact absurd ht (by decide)
  ·
    cases t
    case twistedG2 => exact absurd hmod.1.2.2.2.1 (by norm_num)
    case twistedF4 =>
      rcases hq35 with rfl | rfl
      · exact hRee X f hmod D hD hcard
      · obtain ⟨E, hE, hEcard⟩ := exists_sub_card_pow_three Nat.prime_five hD hcard
        exact Q1327C.false_of_pow_three_ree_five hmod Nat.prime_five le_rfl hE hEcard
    case Tits => exact false_tits hmod hq35 hcard
    all_goals exact absurd ht (by decide)
  ·
    exact false_suzuki hmod hq hq35 hD hcard

end CFSG.RankThree.PartOne.BRANCH
