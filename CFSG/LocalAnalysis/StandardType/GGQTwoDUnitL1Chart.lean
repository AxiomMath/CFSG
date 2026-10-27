module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Chart

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]


theorem ggQTwoDUnit_chartL (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} (e' : Fin m ≃ ι) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hL : qtwoOrthL.compl G L 𝒦) :
    QTwoDL1Chart p B Bs L := by
  obtain ⟨F0, iF, iFin, iC, ψ, ε, h⟩ := ggQTwoDUnit_base hRig hTBF hWI hcfg e' hm hM hL
  exact Or.inl ⟨F0, iF, iFin, iC, m, ψ, h.card_field, h.hyp, h.range, h.diag,
    h.card_bs_eq (by omega)⟩

end CFSG.StandardType.QTwo

end
