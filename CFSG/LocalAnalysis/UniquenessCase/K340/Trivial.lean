module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.LocalAnalysis.UniquenessCase.K340.Vocab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

variable {G : Type} [Group G] [Finite G]

private theorem pCoreOf_le_of_isSylowOf {H T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) :
    CFSG.Open.pCoreOf 2 H ≤ T := by
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf T H :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hT
  exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT'

private theorem thompsonJ_pCoreOf_eq {H T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H)
    (hJQ : thompsonJ T ≤ CFSG.Open.pCoreOf 2 H) :
    CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H) = CFSG.Quasithin.thompsonJ T := by
  have hQT : CFSG.Open.pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowOf hT
  have h1 : CFSG.Quasithin.thompsonJ T ≤ CFSG.Open.pCoreOf 2 H := by
    rwa [← thompsonJ_eq_quasithin T]
  exact CFSG.Quasithin.B6.thompsonJ_eq_of_le h1 hQT

private theorem conjClosure_omegaOneZJ_eq {H T X : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H)
    (hJQ : thompsonJ T ≤ CFSG.Open.pCoreOf 2 H)
    (hX : X ≤ Subgroup.normalizer (thompsonJ T : Set G)) :
    conjClosure X (omegaOneZJ (CFSG.Open.pCoreOf 2 H)) =
      omegaOneZJ (CFSG.Open.pCoreOf 2 H) := by
  have hJeq := thompsonJ_pCoreOf_eq hT hJQ
  have hFmap : ∀ x ∈ X,
      (omegaOneZJ (CFSG.Open.pCoreOf 2 H)).map (MulAut.conj x).toMonoidHom =
        omegaOneZJ (CFSG.Open.pCoreOf 2 H) := by
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set G) := by
      rw [← thompsonJ_eq_quasithin T]
      exact hX hx
    have hJtmap : (CFSG.Quasithin.thompsonJ T).map (MulAut.conj x).toMonoidHom =
        CFSG.Quasithin.thompsonJ T :=
      CFSG.Quasithin.map_conj_eq_of_mem_normalizer hxN
    calc
      (omegaOneZJ (CFSG.Open.pCoreOf 2 H)).map (MulAut.conj x).toMonoidHom
          = (CFSG.Quasithin.omegaOneCenterOf
              (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H))).map
              (MulAut.conj x).toMonoidHom := by
            rw [omegaOneZJ_eq_quasithin (CFSG.Open.pCoreOf 2 H)]
      _ = CFSG.Quasithin.omegaOneCenterOf
              ((CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H)).map
                (MulAut.conj x).toMonoidHom) :=
            CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv (MulAut.conj x)
              (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H))
      _ = CFSG.Quasithin.omegaOneCenterOf
              ((CFSG.Quasithin.thompsonJ T).map (MulAut.conj x).toMonoidHom) := by rw [hJeq]
      _ = CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) := by rw [hJtmap]
      _ = CFSG.Quasithin.omegaOneCenterOf
              (CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 H)) := by rw [hJeq]
      _ = omegaOneZJ (CFSG.Open.pCoreOf 2 H) :=
            (omegaOneZJ_eq_quasithin (CFSG.Open.pCoreOf 2 H)).symm
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun K hK => ?_
    obtain ⟨x, hx, rfl⟩ := hK
    exact (hFmap x hx).le
  · have h1 : (omegaOneZJ (CFSG.Open.pCoreOf 2 H)).map
        (MulAut.conj (1 : G)).toMonoidHom ∈
        conjSetOf X (omegaOneZJ (CFSG.Open.pCoreOf 2 H)) := ⟨1, X.one_mem, rfl⟩
    have h2 : omegaOneZJ (CFSG.Open.pCoreOf 2 H) ≤
        (omegaOneZJ (CFSG.Open.pCoreOf 2 H)).map (MulAut.conj (1 : G)).toMonoidHom := by
      rw [hFmap 1 X.one_mem]
    exact h2.trans (le_iSup₂_of_le _ h1 le_rfl)

private theorem le_normalizer_omegaOneZJ_pCoreOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer (omegaOneZJ (CFSG.Open.pCoreOf 2 H) : Set G) := by
  have hF_equiv : ∀ (φ : G ≃* G) (Y : Subgroup G),
      ((fun Z => CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ Z)) Y).map
          φ.toMonoidHom =
        (fun Z => CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ Z))
          (Y.map φ.toMonoidHom) := by
    intro φ Y
    rw [CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv,
      CFSG.Quasithin.thompsonJ_map_mulEquiv]
  have hNQ : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hNF : H ≤ Subgroup.normalizer
      ((fun Z => CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ Z))
        (CFSG.Open.pCoreOf 2 H) : Set G) :=
    hNQ.trans (CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv hF_equiv _)
  rw [omegaOneZJ_eq_quasithin (CFSG.Open.pCoreOf 2 H)]
  exact hNF

private theorem thompsonJ_le_self (H : Subgroup G) : thompsonJ H ≤ H := by
  rw [thompsonJ_eq_quasithin H]
  exact CFSG.Quasithin.B6.thompsonJ_le H

theorem first_of_thompsonJ_le_pCoreOf {H T X : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H)
    (hJQ : thompsonJ T ≤ CFSG.Open.pCoreOf 2 H)
    (hX : X ≤ Subgroup.normalizer (thompsonJ T : Set G)) :
    thompsonJ H ≤
      Subgroup.normalizer (conjClosure X (omegaOneZJ (CFSG.Open.pCoreOf 2 H)) : Set G) := by
  rw [conjClosure_omegaOneZJ_eq hT hJQ hX]
  exact (thompsonJ_le_self H).trans (le_normalizer_omegaOneZJ_pCoreOf H)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
