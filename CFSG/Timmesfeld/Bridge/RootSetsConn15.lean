module

public import CFSG.Timmesfeld.Bridge.RootSetsConn14
public import CFSG.Timmesfeld.Exceptional.CaseIThm31
public import CFSG.Timmesfeld.Bridge.OddTranspThird
public import CFSG.Timmesfeld.Bridge.RootSetsConn13

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

@[expose] def Step6ThreeClassesHyp : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (a b c x z : G) (P : Subgroup G), ConnCex D →
    Step6 D a b c x z P → ThreeClasses D x P

theorem disconnectedNoPolarInput_of (hB : OddTranspBender) (hT : OddTranspThirdKind)
    (hIII : Step6ThreeClassesHyp) : DisconnectedNoPolarInput := by
  intro G _ D hS hdisc hsimple hfaith hm2 u hu v hv huv hne
  by_contra hnD
  have hC : ConnCex D := ⟨hS, hdisc, hsimple, hfaith, hm2⟩
  obtain ⟨c, x, z, P, h⟩ := hC.exists_step6 hu hv hne huv hnD
  exact h.false_of_threeClasses hB (step6ThreeProductHyp hB hT) hC (hIII G D _ _ _ _ _ P hC h)

theorem tim75Thm31_of (hB : OddTranspBender) (hT : OddTranspThirdKind)
    (hIII : Step6ThreeClassesHyp) : Moufang.Tim75Thm31 := fun _ _ _ h =>
  commConnected_of_asc73 (asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo)
    (disconnectedNoPolarInput_of hB hT hIII) h

theorem tim75Thm31_of' (hB : OddTranspBender) (hIII : Step6ThreeClassesHyp) :
    Moufang.Tim75Thm31 :=
  tim75Thm31_of hB OddTransp.oddTranspThirdKind hIII

end CFSG.Timmesfeld.Bridge
