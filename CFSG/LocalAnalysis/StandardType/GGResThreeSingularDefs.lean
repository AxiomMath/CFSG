module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggSingularBaseLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∨ lab.tag = .twA) ∧ p ∣ lab.rank + 1 ∧
      ¬ (lab.rank = 5 ∧ ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)))) ∨
    (lab.tag = .E6 ∧ p = 3)

@[expose] def GGResMultiNodeRestThreeSingularInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    ((GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
          p Bs L) ∨
      (GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
          p Bs K)) ∧
    ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K)

end CFSG.StandardType

end
