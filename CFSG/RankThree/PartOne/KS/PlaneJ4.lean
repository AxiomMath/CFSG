module

public import CFSG.RankThree.PartOne.KS.Assembly
public import CFSG.RankThree.PartOne.KS.PlaneOddGeneric
public import CFSG.RankThree.PartOne.S11c.J4Plane
public import CFSG.Sporadic.Schreier.J4SOutOdd

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem odd_card_outer_of_J4
    {T : Type} [Group T] (e : T ≃* Carrier .J4) : Odd (Nat.card (Outer T)) := by
  rw [@Sporadic.J4Schreier.card_outer_congr T Sporadic.J4.J _ (Subgroup.toGroup _)
    (e.trans (Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat))]
  exact Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order

theorem sporadicPlaneOdd_J4 :
    SporadicPlaneOdd (Carrier .J4) := by
  intro T _ _ hs hnab hTA p hp hp3
  obtain ⟨e⟩ := hTA
  exact planeLocalCoreOdd_of_planes_trivial hp hp3 (conj_injective_of_simple hs hnab)
    (isPGroup_two_le_inner_of_odd_outer (odd_card_outer_of_J4 e))
    (fun E U hpl => eq_bot_of_planeOn_J4 hs hnab ⟨e⟩ hpl)

end CFSG.RankThree.PartOne
