module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsTools
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof1514

theorem card_eq_of_isTripleCover {X S : Type*} [Group X] [Group S] (h : Sec4.IsTripleCover X S) :
    Nat.card X = Nat.card S * 3 := by
  obtain ⟨hz, ⟨φ⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr φ.toEquiv, hz]

theorem isSimpleGroup_of_mulEquiv_alternating {X : Type*} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (φ : X ≃* alternatingGroup (Fin n)) : IsSimpleGroup X := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  exact φ.isSimpleGroup

end Proof1514

open Proof1514

end CFSG.RankThree.PartTwo.Sec15
