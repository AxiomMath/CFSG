module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44d
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46e
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHHolds
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre41c

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

@[expose] def S43_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → Odd (Nat.card (Opp 3 (Cen (b * b₁))))

theorem ff84_4_3_of_odd
    (h23 : FF84_2_3)
    (hodd : S43_odd) : FF84_4_3 := fun G _ _ b L B K b₁ b₂ h =>
  ⟨hodd G b L B K b₁ b₂ h,
    Z1_of_odd (a8Model_of_hyp h.hyp) h (ff84_4_1 h23 G b L B K b₁ b₂ h).2
      (hodd G b L B K b₁ b₂ h)⟩

theorem ff84_4_4_of_4_3
    (h23 : FF84_2_3)
    (h43 : FF84_4_3) : FF84_4_4 := fun G _ _ b L B K b₁ b₂ h => by
  have hodd := (h43 G b L B K b₁ b₂ h).1
  have hZ := (h43 G b L B K b₁ b₂ h).2
  have hA := a8Model_of_hyp h.hyp
  have hX := S44_X_trivial hA h (ff84_4_1 h23 G b L B K b₁ b₂ h).2 hodd
  exact ⟨hX, S44_Y_trivial lemmaH_holds hA h hZ hX hodd⟩

theorem ff84_4_6_of_4_4
    (h23 : FF84_2_3)
    (h43 : FF84_4_3) (h44 : FF84_4_4) : FF84_4_6 := fun G _ _ b L B K b₁ b₂ h =>
  S46_main (a8Model_of_hyp h.hyp) h (h43 G b L B K b₁ b₂ h).2 (h44 G b L B K b₁ b₂ h).1
    (h44 G b L B K b₁ b₂ h).2 (ff84_4_1 h23)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
