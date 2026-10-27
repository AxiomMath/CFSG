module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelAux
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelHom

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_model {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hA1 : GGB2derSympKnown) (hcfg : GGConfig 3 B Bs x L D J)
    (hJ : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (r : ℕ) (_ : NeZero r),
      Nat.card K = 2 ∧ 3 ≤ r ∧
      ∃ (ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r))
        (β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)), GGB2derModelProp B L hBL ψ β := by
  obtain ⟨K, _, _, _, r, _, hK, hr, ψ, hsurj, hker, hex⟩ := ggB2der_model_aux hA1 hcfg hJ hBL
  obtain ⟨β, hβ⟩ := ggB2der_beta_of_exists (hBL := hBL) hsurj hex
  exact ⟨K, inferInstance, inferInstance, inferInstance, r, inferInstance, hK, hr, ψ, β,
    ⟨hsurj, hker, hβ⟩⟩

end CFSG.StandardType
