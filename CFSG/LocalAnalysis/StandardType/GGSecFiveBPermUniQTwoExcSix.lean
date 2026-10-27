module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcSixCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveUnitarySixCenterAction
import CFSG.LocalAnalysis.StandardType.GGSecFiveUnitarySixCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly Line63.H5 QTwoExcSix

theorem GGSecFiveRouteCfg.false_of_uniQTwoSix_twoCenter_ne_bot
    (hRig : GGLabelRigidInput) (hU62 : GGU62OuterDiagInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (eta : ↥Bs ≃* (Fin 6 → Multiplicative (ZMod p)))
    (hJoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 6 p)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull 6 p)
    (hB : B = Bs)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel 6 p lab ∧ lab.n ≤ 1) p Bs L)
    (hZ : Line63.H5.twoCenter L ≠ ⊥) : False := by
  obtain ⟨rfl, K, _, _, _, hN, eta', σ, χ, hK4, heta', hF⟩ :=
    exists_redUniLFrame_of_uniQTwoSix hRig hR eta hA hLab
  have hS : LargeEvenSStar 3 B x L := hR.1.1.1.2.2.2.2.2.2.1
  exact false_of_twoCenter_ne_bot hR.1.1 hB hN eta hJoin hA hZ
    (ggSecFiveBPermUniQTwoExc_fixed_free_b1 hRig hU62 hR eta hA hLab)
    (exists_eq_mul_central_of_commute_redFrame hN eta eta' heta' hK4 hF hS.2.2.2.1.2.2.1
      fun _ hv => mem_of_prod_eq_one hN eta hA hv)


theorem ggSecFiveBPermUniQTwoExcSixInput_of_u62
    (hRig : GGLabelRigidInput) (hU62 : GGU62OuterDiagInput) :
    GGSecFiveBPermUniQTwoExcSixInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ _ _ eta hJoin hA _ _ _ hB hLab hZ
  exact (hR.false_of_uniQTwoSix_twoCenter_ne_bot hRig hU62 eta hJoin hA hB hLab hZ).elim

end CFSG.StandardType

end
