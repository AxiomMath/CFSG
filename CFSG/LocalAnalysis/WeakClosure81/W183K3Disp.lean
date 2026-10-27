module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3DispOne
public import CFSG.LocalAnalysis.WeakClosure81.W183K3DispTwo
public import CFSG.LocalAnalysis.WeakClosure81.W183FourConj
public import CFSG.LocalAnalysis.WeakClosure81.W183Q
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Dynkin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open W183K3

variable {G : Type} [Group G] [Finite G]

private theorem w183k3disp_conj_cases_of_dvd (h210 : Asch2_10)
    {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (h3 : 3 ∣ (kerMV V H).relIndex L) :
    (∀ t ∈ D.T, conjSubgroup L t = L) ∨
      ∃ t ∈ D.T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t := by
  have hr : CFSG.Open.pRank 3 H ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 H]
    exact (not_concl182_iff.mp h2).1.1
  exact w183four_conj_cases
    (h210 G H D.T (kerMV V H) L c.hyp.kgroup c.hyp.isSylowIn_T hr hL h3 hLT)

theorem tail1812FourFreeKStarBig_of_leaves
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hO : LieOrderFormulasInput) (hB : ListBNonabelian) (rows : Br3Rows) (leaves : Br3Leaves) :
    Tail1812FourFreeKStarBig G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK hbig g hgT hgK hgi hA
  obtain ⟨hOK, L, hL, hLT, hsh⟩ :=
    MinCex183.exists_component182_ker_AS h172 h5_4 h5_11 h5_13 c h2
  have hN : calNIn H D.T = {H ⊓ D.M} := c.calNIn_eq_AS h5_11 h5_13
  have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := w183k3_gam_of_not_le_ker x hgi hgK
  obtain ⟨Kk, F, hsoc, hKk, hperf, hFeq, hle, hcent, hodd⟩ :=
    MinCex183.kernel_182 hB h162 h172 h5_4 h5_11 h5_13 c h2 M hgam hgT
  have hker : KStarData Kk F := ⟨hsoc, hperf, hFeq, hle, hcent, hodd⟩
  have hKne : Kk ≠ ⊥ := w183k3_kk_ne_bot M hKk (hL.2.1.trans hL.2.2.1) hK
  have hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => KShapeList X) := by
    have h := hasQuotShape_kshape_of_shape54 hsh
    rwa [hOK] at h
  have hdvd : 3 ∣ (kerMV V H).relIndex L := kshape_three_dvd hO hX
  have hcases := w183k3disp_conj_cases_of_dvd rows.h210 c h2 hL hLT hdvd
  have hdyn2 : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsAlt X 6 ∨ IsL3 X 1) →
      ∃ t ∈ D.T, ActsOnDynkinMod (kerMV V H) L t := fun hX2 => by
    obtain ⟨t, htT, ht⟩ := c.exists_dynkin_182 (asch5_4Dynkin_of_asch5_4 h5_4) h2
      (hOK.symm ▸ hL) hLT (hOK.symm ▸ hX2)
    exact ⟨t, htT, hOK ▸ ht⟩
  rcases hcases with hn | ⟨t, htT, hne, hall⟩
  · exact w183k3_disp_one hGA hO rows leaves x M hN hker hKk hKne hOK hL
      (w183four_le_normalizer hLT hn) hLT hsh hdyn2 hbig hgam
  · exact w183k3_disp_two hGA hO rows leaves x M hN hker hKk hKne hOK hL hLT hsh
      htT hne hall hdyn2 hbig hgam

end CFSG.LocalAnalysis.WeakClosure81

end
