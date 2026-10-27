module

public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section Tag

section Minuscule

open CFSG.LieType.Steinberg.Minuscule

private theorem rankOneModel_e7 (k : Type) [Field k] :
    GGRankOneModel (e7Datum k) k := by
  unfold GGRankOneModel
  obtain ⟨O⟩ := e7_nonempty_commOrder k
  have hE := (e7Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E7 k
    posDef_cartan_E7 neighbour_E7 O).2
  refine ⟨e7Data_valid.xm k, e7Data_valid.commC k, O, hE, fun h hh i => ?_⟩
  refine PsiDiag.Minu.conj_xm_eq_of_mem_normalizer e7Data_valid k ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots i)

private theorem rankOneModel_e6 (k : Type) [Field k] :
    GGRankOneModel (e6Datum k) k := by
  unfold GGRankOneModel
  obtain ⟨O⟩ := e6_nonempty_commOrder k
  have hE := (e6Data_valid.minDatum_chevalleyExtras_commC isFiniteType_cartan_E6 k
    posDef_cartan_E6 neighbour_E6 O).2
  refine ⟨e6Data_valid.xm k, e6Data_valid.commC k, O, hE, fun h hh i => ?_⟩
  refine PsiDiag.Minu.conj_xm_eq_of_mem_normalizer e6Data_valid k ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots i)

end Minuscule

section Adjoint

open CFSG.LieType.Steinberg.Adjoint

private theorem rankOneModel_e8 (k : Type) [Field k] :
    GGRankOneModel (e8Datum k) k := by
  unfold GGRankOneModel
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e8Datum k).isFiniteType
    (Dv := (e8Datum k).divisible) rfl
  obtain ⟨C, -, hC⟩ := e8_commutatorFormula k O
  have hE := e8_chevalleyExtras k O C hC
  refine ⟨e8Par k, C, O, hE, fun h hh i => ?_⟩
  exact PsiDiag.ggTorus_conj_single (e8_isCTGroupDatum k) (e8_steinbergExtras k) hE.param i
    (PsiDiag.Adj.torus_le_scalarSub hE i) hh

end Adjoint

theorem ggRankOneModel_E6 {n f : ℕ} (hadm : StatedLieAdmissible .E6 n 2 f)
    (hrank : 3 ≤ bnRank .E6 n) : GGRankOneModel (ggU .E6 n f).D (GaloisField 2 f) := by
  exact rankOneModel_e6 (GaloisField 2 f)

theorem ggRankOneModel_E7 {n f : ℕ} (hadm : StatedLieAdmissible .E7 n 2 f)
    (hrank : 3 ≤ bnRank .E7 n) : GGRankOneModel (ggU .E7 n f).D (GaloisField 2 f) := by
  exact rankOneModel_e7 (GaloisField 2 f)

theorem ggRankOneModel_E8 {n f : ℕ} (hadm : StatedLieAdmissible .E8 n 2 f)
    (hrank : 3 ≤ bnRank .E8 n) : GGRankOneModel (ggU .E8 n f).D (GaloisField 2 f) := by
  exact rankOneModel_e8 (GaloisField 2 f)

end Tag

end CFSG.StandardType
