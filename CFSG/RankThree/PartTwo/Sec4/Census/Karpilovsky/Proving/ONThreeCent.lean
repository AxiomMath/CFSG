module

public import CFSG.RankThree.Native.ONThreeCentralizer
public import CFSG.RankThree.Native.ONThreeFusion
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.SevenCent

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.RankThree.Native

theorem card_centralizer_three_ON
    {T : Type} [Group T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.ON) {u : T} (hu : orderOf u = 3) :
    Nat.card (Subgroup.centralizer ({u} : Set T)) = 3240 := by
  have heu : orderOf (e u) = 3 := by rw [MulEquiv.orderOf_eq, hu]
  obtain ⟨k, hk⟩ := onThree_fusion heu orderOf_onThreeElt
  have h3 := card_centralizer_onThreeElt
  rw [← hk, Coordinator.KF148ONA7.card_centralizer_conj] at h3
  exact (@Coordinator.KF148ONA7.card_centralizer_map_equiv T inferInstance
    CFSG.Blueprint.NativeSporadic.ON inferInstance e u).symm.trans h3

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
