module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2MapInj
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ProdPCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaPlusLevi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaPlusLine
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSL
import CFSG.Open.StatedAPI
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open CFSG.AGLEmbedding.LeviBlock

private instance finite_linearEquiv_plus_Q15 {K : Type} [Field K] [Finite K] {r : ℕ} :
    Finite ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  finite_plusAut r

private noncomputable def slEquivStatedSL_Q15 (n : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K ≃* CFSG.Open.StatedSL n K :=
  (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL n K).symm)

private lemma isPerfect_SL2_Q15 {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Group.isPerfect_def.mpr (isQuasisimple_SL_of_four_le h4 (le_refl 2)).1

private lemma pCore_SL2_Q15 {K : Type} [Field K] [Finite K] [CharP K 2] :
    CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  let e := slEquivStatedSL_Q15 2 K
  have h := CFSG.pCore_map_iso 2 e
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedSL_eq_bot 2 2] at h
  exact (Subgroup.map_eq_bot_iff_of_injective
    (CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K)) e.injective).mp h

private theorem nonempty_bar2_hinf_plusFlagStab_three_Q15 {K : Type} [Field K] [Finite K]
    [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨A, hA, β, S, eS, hker, hSR, hcomm⟩ :=
    exists_leviHom_plusFlagStab_three (K := K)
  letI : Group A := hA
  obtain ⟨eS⟩ := eS
  refine nonempty_bar2_hinf_equiv_of_leviHom_of_equiv
    (plusFlagStab K 3 ({1} : Finset ℕ)) β hker S hSR hcomm eS ?_ ?_
  · exact isPerfect_prod (isPerfect_SL2_Q15 h4) (isPerfect_SL2_Q15 h4)
  · exact pCore_prod_eq_bot (pCore_SL2_Q15 (K := K)) (pCore_SL2_Q15 (K := K))

theorem nonempty_bar2_hinf_lineStab_statedOmegaPlus_three {K : Type} [Field K] [Finite K]
    [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (lineStab (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨f, hf, hmap⟩ := exists_injective_hom_map_lineStab_eq_plusFlagStab (K := K)
  have h2 := nonempty_bar2_hinf_map_of_injective f hf
    (lineStab (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl ⟨0, by omega⟩) 1))
  rw [hmap] at h2
  obtain ⟨e2⟩ := h2
  obtain ⟨e3⟩ := nonempty_bar2_hinf_plusFlagStab_three_Q15 (K := K) h4
  exact ⟨e2.trans e3⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
