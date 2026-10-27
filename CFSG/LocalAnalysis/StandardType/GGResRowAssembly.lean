module

public import CFSG.LocalAnalysis.StandardType.GGResRowOnEmpty
public import CFSG.LocalAnalysis.StandardType.GGResRowSympLinOn
public import CFSG.LocalAnalysis.StandardType.GGResRowF4ThreeOn
public import CFSG.LocalAnalysis.StandardType.GGResXDatumE6Two
public import CFSG.LocalAnalysis.StandardType.GGResXDatumTwE6Dvd
public import CFSG.LocalAnalysis.StandardType.GGResXDatumTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTBWeylRowResRest2Cases
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResRows_label_false {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlab : LargeEvenInLambda2 lab)
    (h : ((((GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧ ¬ GGF4ThreeLabel p lab) ∧
        ¬ GGNbrNonSplitE6TwoLabel p lab) ∧
        ¬ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1)) ∧ ¬ GGTwE6BadLabel p lab) :
    False := by
  obtain ⟨⟨⟨⟨⟨h0, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩ := h
  rcases ggTBWeylRowResRest2_cases hp hp2 hlab h0 with h1 | h1 | h1 | h1 | h1
  exacts [n1 h1, n2 h1, n3 h1, n4 h1, n5 h1]

theorem ggTBXDatumResInputRest_of_rows
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    (hRk : GGTwE6ThreeNbrRankInput) : GGTBXDatumResInputRest := by
  refine ggTBXDatumResInputRest_of_rest2 ?_
  refine ggTBXDatumResOn_of_sympLin (S := GGTBWeylRowResRest2) hRig hcyc ?_
  refine ggTBXDatumResOn_of_f4Three
    (S := fun p lab => GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) hRig hcyc ?_
  refine ggTBXDatumResOn_of_e6Two hRig hcyc
    (S := fun p lab => (GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧
      ¬ GGF4ThreeLabel p lab) ?_
  refine ggTBXDatumResOn_of_twE6Dvd hRig hcyc
    (S := fun p lab => ((GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧
      ¬ GGF4ThreeLabel p lab) ∧ ¬ GGNbrNonSplitE6TwoLabel p lab) ?_
  refine ggTBXDatumResOn_of_twE6Three hRk hRig hcyc
    (S := fun p lab => (((GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧
      ¬ GGF4ThreeLabel p lab) ∧ ¬ GGNbrNonSplitE6TwoLabel p lab) ∧
      ¬ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1)) ?_
  exact ggTBXDatumResOn_of_empty fun p lab hp hp2 hlab h => ggResRows_label_false hp hp2 hlab h

theorem ggPZNbrResDatumRest_of_rows
    (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    (hRk : GGTwE6ThreeNbrRankInput) : GGPZNbrResDatumRest := by
  refine ggPZNbrResDatumRest_of_rest2 ?_
  refine ggPZNbrResDatumOn_of_sympLin (S := GGTBWeylRowResRest2) hRig hcyc ?_
  refine ggPZNbrResDatumOn_of_f4Three
    (S := fun p lab => GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) hRig hcyc ?_
  refine ggPZNbrResDatumOn_of_e6Two hRig hcyc
    (S := fun p lab => (GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧
      ¬ GGF4ThreeLabel p lab) ?_
  refine ggPZNbrResDatumOn_of_twE6Dvd hRig hcyc
    (S := fun p lab => ((GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧
      ¬ GGF4ThreeLabel p lab) ∧ ¬ GGNbrNonSplitE6TwoLabel p lab) ?_
  refine ggPZNbrResDatumOn_of_twE6Three hRk hRig hcyc
    (S := fun p lab => (((GGTBWeylRowResRest2 p lab ∧ ¬ GGResAN2Label p lab) ∧
      ¬ GGF4ThreeLabel p lab) ∧ ¬ GGNbrNonSplitE6TwoLabel p lab) ∧
      ¬ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1)) ?_
  exact ggPZNbrResDatumOn_of_empty fun p lab hp hp2 hlab h => ggResRows_label_false hp hp2 hlab h

end CFSG.StandardType

end
