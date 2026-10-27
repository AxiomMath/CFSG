module

public import CFSG.RankThree.PartTwo.Sec15.Item1423ProofLocal
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem rank3II_14_23 (h45 : Sec4.Item4_5) (hSz : KFacts.KPSz)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A) :
    Item14_23 A L := by
  intro _ _ _ E hE1 _ hEA hEL X hX hEX
  have hD := h.toSec13Data
  have : IsSimpleGroup G := h.isSimpleGroup
  have hX3 : ¬ 3 ∣ Nat.card X := (isPiSubgroup_piCompl_iff Nat.prime_three X).mp hX.2.1
  have hXA : X ⊔ A ≠ ⊤ := by
    intro htop
    have hX1 : X ≠ ⊥ := fun hb => hE1 (le_bot_iff.mp (hb ▸ hEX))
    have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (htop ▸ sup_le Subgroup.le_normalizer hX.2.2))
    rcases hXn.eq_bot_or_eq_top with hb | ht
    · exact hX1 hb
    · apply hX3
      rw [ht, Subgroup.card_top]
      exact (show 3 ∣ 27 by norm_num).trans (hD.card_eq ▸ Subgroup.card_subgroup_dvd_card A)
  exact Proof1423.isSolvable_normalClosureSub_of_forall hX3 fun K hK =>
    Proof1423.le_thetaQuotCentralizer_of_item142 h45 hSz h h142 hEA hEL hX hEX hXA hK

theorem item14_23R_of (h45 : Sec4.Item4_5) (hSz : KFacts.KPSz)
    (h142 : Item142R) : Item14_23R :=
  fun G _ _ A c L h => rank3II_14_23 h45 hSz h.toSec14Std (h142 G A c L h)

end CFSG.RankThree.PartTwo.Sec15
