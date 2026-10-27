module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open Matrix (SpecialLinearGroup)

variable {G : Type} [Group G] [Finite G]

private theorem not_thompsonJ_le_centralizer_VZ' {k : Type} [Field k] [Finite k] [CharP k 2]
    {T : Subgroup G} {π : G →* SpecialLinearGroup (Fin 2) k}
    (h : SeedSetting T π) (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJT : ¬ thompsonJ T ≤ CFSG.pCore 2 G) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T ⊤ : Set G) := by
  intro hle
  apply hJT
  have h1 : thompsonJ T ≤ π.ker ⊓ T :=
    le_inf (hle.trans (h.centralizer_VZ_le_ker hnc)) (B6.thompsonJ_le T)
  rwa [h.ker_inf_eq] at h1

private theorem thompsonJ_sup_centralizer_sup_eq_top' {k : Type} [Field k] [Finite k] [CharP k 2]
    {T : Subgroup G} {π : G →* SpecialLinearGroup (Fin 2) k}
    (h : SeedSetting T π) (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJT : ¬ thompsonJ T ≤ CFSG.pCore 2 G) :
    thompsonJ (⊤ : Subgroup G) ⊔ Subgroup.centralizer (VZ T ⊤ : Set G) ⊔ T = ⊤ := by
  haveI : (VZ T ⊤).Normal := normal_VZ_top T
  haveI : (thompsonJ (⊤ : Subgroup G)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (B6.le_normalizer_thompsonJ ⊤))
  refine h.sup_eq_top (C := thompsonJ (⊤ : Subgroup G) ⊔ Subgroup.centralizer (VZ T ⊤ : Set G))
    (h.pCore_le_centralizer_VZ.trans le_sup_right) fun hle => ?_
  apply hJT
  have h1 : thompsonJ T ≤ π.ker ⊓ T :=
    le_inf ((B6.thompsonJ_le_of_sylow h.sylow).trans (le_sup_left.trans hle)) (B6.thompsonJ_le T)
  rwa [h.ker_inf_eq] at h1

theorem exists_isSeed_of_setting' {k : Type} [Field k] [Finite k] [CharP k 2] {T : Subgroup G}
    {π : G →* Matrix.SpecialLinearGroup (Fin 2) k}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.SeedSetting T π)
    (hnc : ⁅(⊤ : Subgroup G), CFSG.Open.quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJT : ¬ CFSG.Quasithin.thompsonJ T ≤ CFSG.pCore 2 G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = T) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : G →* Matrix.SpecialLinearGroup (Fin 2) F)
      (ψ : CFSG.QuasithinUnique.Setup.Campbell.Ecore G →* Multiplicative (Fin 2 → F)),
      CFSG.QuasithinUnique.Setup.Campbell.IsSeed P ρ
        (CFSG.QuasithinUnique.Setup.Campbell.Ecore G) ψ := by
  haveI := CFSG.Adapters.certificate43_holds
  haveI : (VZ T ⊤).Normal := normal_VZ_top T
  obtain ⟨M, hmin⟩ := h.exists_minParabolic
  have hfam := CFSG.AGLEmbeddingD2.Tits.E23.famI_e23FamGen h.isElemAbelian_VZ hmin
    (CFSG.AGLEmbeddingD2.Tits.E23.minPar_of_minParabolic hmin) h.charTwo h.isTwoReducedIn_VZ
    (not_thompsonJ_le_centralizer_VZ' h hnc hJT)
  have hVE : VZ T ⊤ ≤ Ecore G := by
    intro v hv
    have hc := h.VZ_le_center_pCore hv
    rw [pCoreOf_top_eq_pCore_two] at hc
    exact CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mpr
      ⟨hc.1, fun x hx => Subgroup.mem_centralizer_iff.mp hc.2 x hx, h.isElemAbelian_VZ.2 v hv⟩
  exact isSeed_of_e23 h h.isElemAbelian_VZ hfam hVE h.pCore_le_centralizer_VZ
    (h.centralizer_VZ_le_ker hnc) (thompsonJ_sup_centralizer_sup_eq_top' h hnc hJT) P hP hJT

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
