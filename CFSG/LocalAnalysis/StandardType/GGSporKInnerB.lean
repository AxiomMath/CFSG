module

public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.YGroups.DCE.B433Check

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Blueprint

theorem ggSporK_inner_B :
    ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic .B).Group, ∃ g, φ = MulAut.conj g := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : (TauCeti.CFSGIndex.sporadic .B).Group ≃* NativeSporadic.Carrier .B :=
    e.symm.trans (MulEquiv.refl _)
  exact CFSG.ComponentClassification.BMCase.inner_of_equiv e'
    CFSG.RankThree.PartOne.SPOR.allInner_B

end CFSG.StandardType.SporadicShape
