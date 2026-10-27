module

public import CFSG.LocalAnalysis.StandardType.GGForkF1

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggForkWeylExtRestInput_of_affine_indef (hA : GGForkAffineExclRest)
    (hI : GGForkIndefExclRest) : GGForkWeylExtRestInput := by
  intro G _ _ p B Bs x L D J hC hO hID hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK hSA hSB
  obtain ⟨i0, i1⟩ := hI G p B Bs x L D J hC hO hID hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c
    hM hCM hF hlin hlina hind hL hK hSA hSB
  obtain ⟨a0, a1⟩ := hA G p B Bs x L D J hC hO hID hNT y K hN hR hPm Λ M C V ι φ φa h α ha αa b c
    hM hCM hF hlin hlina hind hL hK hSA hSB
  exact ⟨fun hu => (i0 hu).resolve_right (a0 hu), fun hu => (i1 hu).resolve_right (a1 hu)⟩

theorem ggCoxeterForkLabelInput_of_cells (hFix : GGTBFixInput)
    (h5 : GGForkCrossGe5Input) (hA : GGForkAffineExclRest) (hI : GGForkIndefExclRest) :
    GGCoxeterForkLabelInput :=
  ggCoxeterForkLabelInput_of_fix hFix h5 (ggForkWeylExtRestInput_of_affine_indef hA hI)

@[expose] def GGRemainderCoxeterLabelKnown : Prop :=
  GGTBFixInput ∧ GGForkCrossGe5Input ∧ GGForkAffineExclRest ∧ GGForkIndefExclRest ∧
    GGCoxeterLabelResidualInput

theorem ggRemainderCoxeterLabel_of_known (h : GGRemainderCoxeterLabelKnown) :
    GGCoxeterForkLabelInput ∧ GGCoxeterLabelResidualInput :=
  ⟨ggCoxeterForkLabelInput_of_cells h.1 h.2.1 h.2.2.1 h.2.2.2.1, h.2.2.2.2⟩

@[expose] def GGRemainderCoxeterLabelSplit : Prop :=
  GGTBFixInput ∧ GGForkCrossGe5MainInput ∧ GGForkCrossGe5ExcInput ∧ GGForkAffineExclRest ∧
    GGForkIndefExclRest ∧ GGCoxeterLabelResidualInput

theorem ggRemainderCoxeterLabel_of_split (h : GGRemainderCoxeterLabelSplit) :
    GGCoxeterForkLabelInput ∧ GGCoxeterLabelResidualInput :=
  ⟨ggCoxeterForkLabelInput_of_cells h.1 (ggForkCrossGe5Input_of_f1_split h.1 h.2.1 h.2.2.1)
    h.2.2.2.1 h.2.2.2.2.1, h.2.2.2.2.2⟩

end CFSG.StandardType
