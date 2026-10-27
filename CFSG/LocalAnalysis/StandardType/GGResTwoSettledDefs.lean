module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSettledDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggTwoSettledEitherLabelL (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
    (p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧ ¬ 3 ∣ lab.rank + 1) ∨
    (p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1)

@[expose] def ggTwoSettledLabelL (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ 6 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
  (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) ∨
    ((lab.tag = .twA ∧ 3 ≤ lab.rank ∨ lab.tag = .twD ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n + 1) ∨
    (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 3) ∨
    (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ lab.rank = 4) ∨
    (p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧ 4 ≤ lab.rank) ∨
    (p = 3 ∧ lab.tag = .A ∧ lab.n = 1 ∧ 5 ≤ lab.rank) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1)

@[expose] def ggTwoSettledLabelK (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1) ∨
    (p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧ ¬ 3 ∣ lab.rank + 1) ∨
    (p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1)

@[expose] def ggTwoResidualLabelL (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank ≤ 5) ∨ lab.tag = .D ∨
      lab.tag = .twD) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ (p = 3 ∧ lab.n = 1)) ∨
    ((lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) ∨
      ((lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ p = 3 ∧ lab.n = 1)) ∨
    (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGResMultiNodeRestTwoSettledInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
    ¬ GGInnerDiagOnLabel ggTwoSettledLabelL p Bs L ∧
    (GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny →
      ¬ GGInnerDiagOnLabel ggTwoSettledLabelK p Bs K) ∧
    ¬ GGInnerDiagOnLabel ggTwoSettledEitherLabelL p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

@[expose] def GGResMultiNodeRestTwoCensusInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
    ¬ GGInnerDiagOnLabel ggTwoSettledLabelL p Bs L ∧
    (GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny →
      ¬ GGInnerDiagOnLabel ggTwoSettledLabelK p Bs K) ∧
    GGInnerDiagOnLabel ggTwoResidualLabelL p Bs L ∧
    ¬ GGInnerDiagOnLabel ggTwoSettledEitherLabelL p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

@[expose] def GGResMultiNodeRestTwoCellInput (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
    ¬ GGInnerDiagOnLabel ggTwoSettledLabelL p Bs L ∧
    (GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny →
      ¬ GGInnerDiagOnLabel ggTwoSettledLabelK p Bs K) ∧
    GGInnerDiagOnLabel S p Bs L ∧
    ¬ GGInnerDiagOnLabel ggTwoSettledEitherLabelL p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L ∧
    ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K ∧
    ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

end CFSG.StandardType

end
