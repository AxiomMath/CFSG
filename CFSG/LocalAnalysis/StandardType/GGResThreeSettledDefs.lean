module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSingularDefs
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggThreeSettledLabelL (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
    (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank)

@[expose] def ggThreeSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenSmallRankLabel p lab ∨ (GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) ∨
    StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] def ggThreeSettledLabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggThreeSmallLabel p lab ∨
    (p = 7 ∧ ((lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1) ∨ (lab.tag = .E6 ∧ lab.n = 1)))

@[expose] def ggThreeSettledE6LabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧
    ((lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1))

@[expose] def ggThreeSettledE6LabelL (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧
    ((lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1))

@[expose] def ggThreeSettledLinTwoLabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ lab.tag = .A ∧ lab.n = 1

@[expose] def ggThreeSettledLinNsLabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1

@[expose] def ggThreeSettledLinSplitLabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGTwASplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def ggThreeNonsingBaseLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab) ∨ GGF4ThreeLabel p lab ∨
    GGTwASplitLabel p lab

@[expose] def ggThreeResidualLabelL (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 6 ≤ lab.rank

@[expose] def ggThreeResidualLabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGResMultiNodeRestThreeSettledInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    ((GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs L ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelL p Bs L) ∨
      (GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinTwoLabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinNsLabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinSplitLabelK p Bs K)) ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

@[expose] def GGResMultiNodeRestThreeCensusInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    ((GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs L ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelL p Bs L ∧
        GGInnerDiagOnLabel ggThreeResidualLabelL p Bs L) ∨
      (GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinTwoLabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinNsLabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinSplitLabelK p Bs K ∧
        GGInnerDiagOnLabel ggThreeResidualLabelK p Bs K)) ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

@[expose] def GGResMultiNodeRestThreeKUnitaryQGeFourJoinInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    (GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      (∃ lab : LargeEvenLabel,
        ggThreeResidualLabelK p lab ∧ 5 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs K) ∧
      ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLinTwoLabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLinNsLabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLinSplitLabelK p Bs K ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L ∧
      ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
      ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K))

@[expose] def GGResMultiNodeRestThreeKUnitaryQGeFourRestInput : Prop :=
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
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K))

end CFSG.StandardType

end
