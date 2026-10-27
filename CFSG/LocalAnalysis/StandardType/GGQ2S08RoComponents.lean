module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_roComponents_full
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel}
    (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ GGLabQTwo 3 labL) (hlab : GGQ2S08BigLabel labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (h3 : ¬ 3 ∣ labL.rank + 1)
    (f : Fin (labL.rank + 1) → M.V) (hf : GGQ2S08ROFrame M f) :
    GGQ2S08ROComponents M f :=
  ggQ2s08_roN_components hRig hS M (n := labL.rank) (by have := hlab.2.2; omega) h3 hMark
    ⟨hLab.1, rfl, hLab.2⟩ hWeyl f hf

end CFSG.StandardType

end
