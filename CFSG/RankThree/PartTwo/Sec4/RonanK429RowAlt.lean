module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.Quasithin.Background.A318POutMore

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_dvd_card_alternatingGroup_le_eight {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 8) :
    ¬ 27 ∣ Nat.card (alternatingGroup (Fin n)) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  interval_cases n <;> norm_num [Nat.factorial]

theorem not_three_dvd_outer_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    ¬ 3 ∣ Nat.card (Outer (alternatingGroup (Fin n))) := by
  by_cases h6 : n = 6
  · subst h6
    exact CFSG.Quasithin.A318P.not_dvd_outer_alternating_six (MulEquiv.refl _) Nat.prime_three
      (by norm_num)
  · exact CFSG.Quasithin.A318P.not_dvd_outer_alternating (by omega) (MulEquiv.refl _)
      Nat.prime_three (by norm_num)

theorem noCfgS429_alternating_le_eight {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) {S : Type} [Group S]
    [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* alternatingGroup (Fin n)) : NoCfgS429 S :=
  noCfgS429_of_autNoE27 (autNoE27_of_mulEquiv_of_noE27 e hs hna
    (not_three_dvd_outer_alternatingGroup hn5)
    (noE27_of_not_dvd (not_dvd_card_alternatingGroup_le_eight hn5 hn8)))

theorem rowSOf429_alternating_le_eight {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) :
    RowSOf429 (alternatingGroup (Fin n)) :=
  rowSOf429_of_noCfg fun _ _ _ hs hna ⟨e⟩ => noCfgS429_alternating_le_eight hn5 hn8 hs hna e

end CFSG.RankThree.PartTwo.Sec4.RonanK429
