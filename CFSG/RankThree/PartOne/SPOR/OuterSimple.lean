module

public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic

public section

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.RankThree.PartOne.SPOR

theorem sporadicHS_outer_le_two :
    Nat.card (Outer (NativeSporadic.Carrier .HS)) ≤ 2 :=
  card_outer_HS_le_two

theorem sporadicOuterOrderLeTwoSimple_holds :
    SporadicOuterOrderLeTwoSimple := by
  intro s hs T _ _ _ _ ⟨e⟩
  have hc : ∀ {n : ℕ}, Nat.card (Outer (NativeSporadic.Carrier s)) ≤ n →
      Nat.card (Outer T) ≤ n :=
    fun h => by rw [Nat.card_congr (equivalence e).toEquiv]; exact h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc (card_outer_Co1.le.trans (by norm_num))
  · exact hc (card_outer_Co2.le.trans (by norm_num))
  · exact hc card_outer_HN.le
  · exact hc (by rcases card_outer_Ly with h | h <;> omega)
  · exact hc (card_outer_Th.le.trans (by norm_num))
  · exact hc (card_outer_B.le.trans (by norm_num))
  · exact (card_outer_M_of_simple e).le.trans (by norm_num)

end CFSG.RankThree.PartOne.SPOR
