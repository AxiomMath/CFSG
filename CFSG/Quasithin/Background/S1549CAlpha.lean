module

public import CFSG.Quasithin.Background.S1549CBasic
public import CFSG.Quasithin.Background.F9Geometry

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G]

theorem exists_alpha {T V L V₁ Vp H : Subgroup G} (h : HypF98 T V L V₁ Vp H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    ∃ c ∈ H, conjSub c (F8.Uγ V H (g : G)) ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) := by
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen s.critical.geodesic (by omega : 2 ≤ _)
  have hV2 := (h.F913_2 s).2 γ₂ hγ₂nb hd
  obtain ⟨c, hc, hcγ⟩ := stab_transitive_on_nbrs hγ₂nb
    (show F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) from (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm)
  have hcH : (c : G) ∈ H := by rwa [stab_γ₁ h.amalgamHypV.le₂] at hc
  have hc1 : c • F8.γ₁ T L H = F8.γ₁ T L H := smul_eq_of_mem_stab hc
  refine ⟨c, hcH, ?_⟩
  have h1 := conjSub_mono (c : G) hV2
  rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hc1, hcγ,
    inf_comm, h.F913_1] at h1
  exact h1

theorem L₁Of_eq_Y0 (h11 : StageLemma14111) (h113 : StageLemma14113) {T Mc M : Subgroup G}
    (h : Hyp153 G T Mc M) :
    L₁Of (Y153 Mc M) (quasithinOmegaOneCenter T) = Y0 T Mc M := by
  rw [L₁Of_eq_oTwoRes_centralizer _ h.lemma_15_3_2_two.2, oTwoRes_eq_oTwoUpper,
    C1Pack153.inf_centralizer_Z_eq h11 h113 h]
  rfl

theorem exists_alpha_Y0 (h11 : StageLemma14111) (h113 : StageLemma14113) {T Mc M V₁ : Subgroup G}
    (hh : Hyp153 G T Mc M) {H : Subgroup G}
    (h : HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g) :
    ∃ c ∈ H, conjSub c (F8.Uγ (VZ T M) H (g : G)) ≤ pCoreOf 2 (Y0 T Mc M ⊔ T) := by
  obtain ⟨c, hc, h1⟩ := exists_alpha h s
  rw [L₁Of_eq_Y0 h11 h113 hh] at h1
  exact ⟨c, hc, h1⟩

end S1549C

end CFSG.Quasithin
