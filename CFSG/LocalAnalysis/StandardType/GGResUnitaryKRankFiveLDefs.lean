module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSettledDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSpEightOmegaEightTwoLabel (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) ∧ lab.rank = 4 ∧ lab.n = 1

@[expose] def GGResMultiNodeRestThreeKUnitaryQGeFourFieldTwoInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    (GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      (∃ lab : LargeEvenLabel,
        ggThreeResidualLabelK p lab ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
          GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs K) ∧
      ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLinTwoLabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLinNsLabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLinSplitLabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L ∧
      ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
      ¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs L ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)) ∧
    GGInnerDiagOnLabel GGSpEightOmegaEightTwoLabel p Bs L

end CFSG.StandardType

end
