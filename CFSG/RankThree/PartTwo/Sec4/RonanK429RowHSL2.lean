module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHRank
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem rank3LeOne_SL2 {F : Type} [Field F] (h3 : (3 : F) ≠ 0) :
    Rank3LeOne (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro E hE
  by_cases hne : ∃ g ∈ E, g ≠ 1
  · obtain ⟨g, hgE, hg1⟩ := hne
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hg3 : g ^ 3 = 1 := hE.2 g hgE
    have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    have hle : E ≤ Subgroup.zpowers g := by
      intro h hh
      have hc := congrArg Subtype.val (hE.1.is_comm.comm (⟨g, hgE⟩ : E) ⟨h, hh⟩)
      exact CFSG.RankThree.PartTwo.Sec19.sl2_commuting_cube_one h3 hg3 hg1 (hE.2 h hh) hc
    haveI : Finite (Subgroup.zpowers g) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers g) := Subgroup.card_le_of_le hle
      _ = 3 := by rw [Nat.card_zpowers, hord]
  · push Not at hne
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hne
    rw [hbot, Subgroup.card_bot]
    norm_num

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
