module

public import CFSG.Quasithin.EmptyFaithful.S146zUETransv
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S146zU

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem exists_setup_Dlt (S : Setting146 G T M)
    (hNT : ∀ b ∈ mcOf T, b ∉ pCoreOf 2 (mcOf T) →
      2 ≤ mIdx (⁅uOfL22 T M, Subgroup.zpowers b⁆ ⊔ quasithinOmegaOneCenter T)
        (quasithinOmegaOneCenter T)) :
    ∃ (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      F8Setup T (VZ T M) (yOfL22 T M) (mcOf T) γ γ' g ∧
      F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G) <
        F8.Uγ (VZ T M) (mcOf T) (g : G) := by
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨-, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  obtain ⟨γ, γ', g, s⟩ := hF98.exists_F8Setup
  refine ⟨γ, γ', g, s, lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_⟩
  obtain ⟨b, hbH, hbQ, hrk⟩ := UE.exists_element_rank_le_one hF98 s hD.symm
  have h2 : 2 ≤ mIdx (⁅conjClosure (VZ T M) (mcOf T), Subgroup.zpowers b⁆ ⊔
      quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) := hNT b hbH hbQ
  omega

end S146zU

end CFSG.Quasithin
