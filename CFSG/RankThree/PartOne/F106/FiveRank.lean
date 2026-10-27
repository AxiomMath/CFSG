module

public import CFSG.RankThree.PartOne.F106.Defs
public import CFSG.RankThree.PartOne.F106.RankClass
public import CFSG.RankThree.PartOne.F106.FiveFin
public import CFSG.RankThree.PartOne.F106.FiveG2
public import CFSG.RankThree.PartOne.F106.FiveTri
public import CFSG.RankThree.PartOne.F106.FiveRee
public import CFSG.RankThree.PartOne.N143.Weyl613Small

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.N143X

@[expose] def U6ThreeRank : Prop :=
  ∀ (T : Type) [Group T], StatedClassicalModel T .PSU 6 2 1 →
    ∀ D : Subgroup T, CFSG.IsElementaryAbelian 3 D → Nat.card D = 3 ^ 5 → False

@[expose] def F4ThreeRank : Prop :=
  ∀ (T : Type) [Group T], UntwistedChevalleyModel T .F4 2 →
    ∀ D : Subgroup T, CFSG.IsElementaryAbelian 3 D → Nat.card D = 3 ^ 5 → False

theorem evenLieFiveRank_of_small
    (hU6 : U6ThreeRank) (hF4 : F4ThreeRank)
    (X : Type) [Group X] [Finite X] (hEven : EvenLieTypeSmall X) (q : ℕ) (hq37 : q = 3 ∨ q = 7)
    (D : Subgroup X) (hD : CFSG.IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 5) : False := by
  have hq : q.Prime := by rcases hq37 with rfl | rfl <;> norm_num
  obtain ⟨t, n, f, hadm, hLie, hsmall⟩ := hEven
  rcases hLie with ⟨ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, rfl, hmod⟩
  ·
    cases t
    case PSL =>
      by_cases h5 : n ≤ 5
      · exact false_psl_five h5 hmod hq hq37 hD hcard
      · obtain ⟨hn67, hf1⟩ : (n = 6 ∨ n = 7) ∧ f = 1 := by
          rcases hsmall with h | h
          · exact absurd h h5
          · exact h
        subst hf1
        exact false_psl_two_five hn67 hmod hq37 hcard
    case PSU =>
      by_cases h5 : n ≤ 5
      · exact false_psu_five h5 hmod hq hq37 hD hcard
      · obtain ⟨hn6, hf1⟩ : n = 6 ∧ f = 1 := by
          rcases hsmall with h | h
          · exact absurd h h5
          · exact h
        subst hn6
        subst hf1
        rcases hq37 with rfl | rfl
        · exact hU6 X hmod D hD hcard
        · exact false_psu_six_two_seven hmod hcard
    case PSp =>
      by_cases h4 : n ≤ 4
      · exact false_psp_five h4 hmod hq hq37 hD hcard
      · exact absurd hsmall h4
    case POmegaOdd => exact absurd rfl hmod.1.2.2.2
    case POmegaPlus =>
      by_cases h4 : n ≤ 4
      · exact false_pomegaPlus_five h4 hmod hq hq37 hD hcard
      · exact absurd hsmall h4
    case POmegaMinus =>
      by_cases h4 : n ≤ 4
      · exact false_pomegaMinus_five h4 hmod hq hq37 hD hcard
      · exact absurd hsmall h4
    all_goals exact hmod.2.elim
  ·
    cases t
    case G2 =>
      rcases hq37 with rfl | rfl
      · exact false_G2_three_five hmod hD hcard
      · obtain ⟨E, hE, hEcard⟩ := exists_sub_card_pow_three_five hq hD hcard
        exact false_G2_prime hmod hq (by norm_num) hE hEcard
    case trialityD4 =>
      rcases hq37 with rfl | rfl
      · exact false_triality_three_five hmod hD hcard
      · obtain ⟨E, hE, hEcard⟩ := exists_sub_card_pow_three_five hq hD hcard
        exact Q1327C.false_of_pow_three_triality_five hmod hq (by norm_num) hE hEcard
    case F4 =>
      have hf1 : f = 1 := hsmall
      subst hf1
      rcases hq37 with rfl | rfl
      · exact hF4 X (by simpa using hmod.2) D hD hcard
      · exact false_F4_two_seven (by simpa using hmod.2) hcard
    case E6 => exact hsmall.elim
    case E7 => exact hsmall.elim
    case E8 => exact hsmall.elim
    case twistedE6 => exact hsmall.elim
    all_goals exact absurd ht (by decide)
  ·
    cases t
    case twistedG2 => exact absurd hmod.1.2.2.2.1 (by norm_num)
    case twistedF4 =>
      rcases hq37 with rfl | rfl
      · exact false_ree_three_five hmod hD hcard
      · obtain ⟨E, hE, hEcard⟩ := exists_sub_card_pow_three_five hq hD hcard
        exact Q1327C.false_of_pow_three_ree_five hmod hq (by norm_num) hE hEcard
    case Tits => exact false_tits_five hmod hq37 hcard
    all_goals exact absurd ht (by decide)
  ·
    exact false_suzuki_five hmod hq hq37 hD hcard

@[expose] def EvenListConverse : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.Blueprint.EvenLieType X → Census3.TheoremThreeList X → EvenLieTypeSmall X

theorem evenLieFiveRank_of_converse
    (hConv : EvenListConverse) (hU6 : U6ThreeRank) (hF4 : F4ThreeRank) : EvenLieFiveRank := by
  intro X _ _ hs hnonab hEven hList q hq37 D hD hcard
  exact evenLieFiveRank_of_small hU6 hF4 X (hConv X hs hnonab hEven hList) q hq37 D hD hcard

end CFSG.RankThree.PartOne.F106
