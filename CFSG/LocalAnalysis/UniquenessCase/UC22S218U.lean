module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22P218a
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_8U (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ n : ℕ, Odd n → IsSp4 (Bar2 L) n →
    ∃ X : Subgroup G, (Nat.card X).Prime ∧ Nat.card X ∣ 2 ^ n - 1 ∧
      X ≤ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) ∧ X ∈ uniqueSet D.M

theorem s21_8Sp4_of_s21_8U {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h211 : S21_1 D Ch) (hU : S21_8U D Ch) : S21_8Sp4 D Ch := by
  intro hH c L hL n hn hX
  have hLM : L ≤ D.M := hL.1.le
  have hML : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1
      (s21_normalSp4_of D Ch hSg h211 hH c L hL n hn hX)
  obtain ⟨X, hXp, hXn, hXle, hXU⟩ := hU hH c L hL n hn hX
  have hX2 : Nat.card X ≠ 2 := by
    rintro h
    rw [h] at hXn
    have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by decide)
    obtain ⟨k, hk⟩ := dvd_pow_self 2 hn0
    obtain ⟨j, hj⟩ := hXn
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨y, hy1⟩ := X.ne_bot_iff_exists_ne_one.1 (by
    intro h
    rw [h, Subgroup.card_bot] at hXp
    exact Nat.not_prime_one hXp)
  have hyo : orderOf (y : G) = Nat.card X := by
    rcases hXp.eq_one_or_self_of_dvd _ (Subgroup.orderOf_dvd_natCard X y.2) with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.1 h)) hy1
    · exact h
  have hzX : zpowers (y : G) = X :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 y.2) (by rw [Nat.card_zpowers, hyo])
  have hXT : ¬ X ≤ normalizer (D.T : Set G) := fun h =>
    uc22p218s_false_of_le_normalizer D Ch h211 hH c hXp hX2 hyo (by rw [hzX]; exact hXU)
      (by rw [hzX]; exact h)
  obtain ⟨t, ht, hout⟩ := exists_not_inner_of_not_le_normalizer D.sylowM.isPGroup
    (D.sylowM.le.trans hML) (D.sylowM.inf_of_le_normalizer hLM hML) hXle hXT
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup ⟨t, ht⟩
  exact ⟨t, ht, actsNontrivOnDiagram_of_not_inner_sp4 hX hn _ (congrArg Subtype.val ha) hout⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
