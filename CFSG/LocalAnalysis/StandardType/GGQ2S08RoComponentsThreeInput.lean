module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseR4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08ROComponentsThreeInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J →
    ∀ (M : GGQ2LDatum 3 Bs L x), M.ShapeA → ∀ {labL : LargeEvenLabel},
      LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL) →
      (labL.tag = .twA ∧ GGLabQTwo 3 labL) → GGQ2S08BigLabel labL →
      GGQ2LabelWeyl labL M.coxeter → Even (labL.rank + 1) → 3 ∣ labL.rank + 1 →
      ∀ f : Fin (labL.rank + 1) → M.V, GGQ2S08ROFrame M f → GGQ2S08ROComponents M f

end CFSG.StandardType

end
