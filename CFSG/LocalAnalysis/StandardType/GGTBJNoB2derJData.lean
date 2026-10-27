module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derYComp

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_J_data {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hA1 : GGB2derSympKnown) (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)} (hM : GGB2derModelProp B L hBL ψ β)
    {y : ↥B} (hyD : (y : G) ∈ D) (hyx : (y : G) ∉ Subgroup.zpowers x) :
    IsPGroup 2 (Subgroup.center ↥L) ∧ (4 ≤ r → Subgroup.center ↥L = ⊥) ∧
      Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y))) = 4 ∧
      (J.subgroupOf L).map ψ =
        ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y))),
          ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers (β y)))⁆ := by
  classical
  obtain ⟨-, -, -, hperf⟩ := GGConfig.data_L hcfg
  obtain ⟨he1, he3, hcomp, hlab⟩ := ggB2der_y_component hcfg hJ hBL hyD hyx
  obtain ⟨hZ2, hZ1, hrest⟩ := hA1.2 K hK r hr ↥L ψ hM.surj hM.ker_eq.le hperf
  exact ⟨hZ2, hZ1, hrest _ he1 he3 (β y) (fun l => hM.conj y l) _ hcomp hlab⟩

end CFSG.StandardType
