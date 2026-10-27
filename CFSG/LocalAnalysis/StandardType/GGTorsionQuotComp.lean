module

public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotSub
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotQuasi

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionQuotComp

theorem ggTorsion_isComponentOf_image {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {δ : MulAut X} {J : Subgroup X}
    (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    IsComponentOf
      (J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))))
      (ggAutFixedSubgroup (ggInducedAut θ δ)) := by
  have hsub := ggTorsion_subnormal_image θ hJ.2.1
  exact ⟨hsub.le, hsub, ggTorsion_quasisimple_image θ hJ.2.2⟩

end TorsionQuotComp

end CFSG.StandardType
