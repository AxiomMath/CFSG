module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.PCore.Construction
import CFSG.LieType.Universal.Spin.Forms
import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.GH74.GLS.Balance.SolvCompBasic
import TauCeti.RepresentationTheory.Subrepresentation
import CFSG.GH74.GLS.Balance.SolvAPIDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin

private noncomputable def plusNatRep (m : ℕ) (K : Type) [Field K] :
    Representation K ↥(CFSG.MatrixModel.isometryCore (StatedQuadPlus m K))
      (Fin m ⊕ Fin m → K) where
  toFun g := Matrix.mulVecLin
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  map_one' := by
    simp only [Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one]
    rfl
  map_mul' g h := by
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul]
    rfl

private theorem plusNatRep_injective (m : ℕ) (K : Type) [Field K] :
    Function.Injective (plusNatRep m K) := by
  intro a b hab
  have hmat : ((a : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      ((b : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
    Matrix.toLin'.injective (by
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
      simpa [plusNatRep] using hab)
  exact Subtype.ext (Units.ext hmat)

private theorem plusNatRep_isIrreducible {K : Type} [Field K] {m : ℕ} (hm : 2 ≤ m) :
    (plusNatRep m K).IsIrreducible := by
  classical
  have hQ : ⇑(quadPlus m K) = StatedQuadPlus m K := coe_quadPlus m K
  have hO : CFSG.MatrixModel.isometryCore (StatedQuadPlus m K) =
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)).comap
        (toLinEquiv (Fin m ⊕ Fin m) K).toMonoidHom := by
    unfold CFSG.MatrixModel.isometryCore
    exact closure_isometries_eq_comap (ι := Fin m ⊕ Fin m) (K := K) hQ
  have hP : ∃ P : Fin 2 → HypPair (quadPlus m K), ∀ i j, i ≠ j → (P i).Orth (P j) :=
    ⟨fun i => plusPair K (Fin.castLE hm i),
      fun _ _ hij => plusPair_orth (fun h => hij (Fin.castLE_injective hm h))⟩
  haveI : Nontrivial (Fin m ⊕ Fin m → K) := by
    refine ⟨0, Pi.single (Sum.inl (⟨0, by omega⟩ : Fin m)) (1 : K), ?_⟩
    intro h
    have := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin m))
    simpa using this
  refine ⟨fun R => ?_⟩
  have hWin : ∀ g ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus m K),
      ∀ x ∈ R.toSubmodule,
      Matrix.mulVecLin ((g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x ∈ R.toSubmodule := by
    intro g hg x hx
    have h := R.apply_mem_toSubmodule
      (⟨g, hg⟩ : ↥(CFSG.MatrixModel.isometryCore (StatedQuadPlus m K))) hx
    simpa [plusNatRep] using h
  have hWelem : ∀ g ∈ elementaryGroup (quadPlus m K), ∀ x ∈ R.toSubmodule,
      g x ∈ R.toSubmodule := by
    intro g hg x hx
    have hgO : (toLinEquiv (Fin m ⊕ Fin m) K).symm g ∈
        CFSG.MatrixModel.isometryCore (StatedQuadPlus m K) := by
      rw [hO]
      exact Subgroup.mem_comap.mpr (by
        simpa using elementaryGroup_le_orthogonalGroup (quadPlus m K) hg)
    have h1 := hWin _ hgO x hx
    rw [Matrix.mulVecLin_apply, ← toLinEquiv_apply, MulEquiv.apply_symm_apply] at h1
    exact h1
  rcases submodule_eq_bot_or_top_of_elementaryGroup_invariant
      (nondegenerate_polarBilin_quadPlus m K) hP R.toSubmodule hWelem with hbot | htop
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (hbot.trans Subrepresentation.toSubmodule_bot.symm))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (htop.trans Subrepresentation.toSubmodule_top.symm))

theorem pCore_statedOmega_plus_eq_bot {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {m : ℕ} (hm : 2 ≤ m) :
    CFSG.pCore p ↥(StatedOmega (StatedQuadPlus m K)) = ⊥ := by
  classical
  let O : Subgroup (GL (Fin m ⊕ Fin m) K) :=
    CFSG.MatrixModel.isometryCore (StatedQuadPlus m K)
  have hΩO : StatedOmega (StatedQuadPlus m K) = ⁅O, O⁆ := rfl
  have hpO : CFSG.pCore p ↥O = ⊥ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible p
      (plusNatRep m K) (plusNatRep_injective m K) (plusNatRep_isIrreducible hm)
  have hΩle : StatedOmega (StatedQuadPlus m K) ≤ O := by
    rw [hΩO]
    exact Subgroup.commutator_le_self O
  have hcomm : (StatedOmega (StatedQuadPlus m K)).subgroupOf O = _root_.commutator ↥O := by
    change (StatedOmega (StatedQuadPlus m K)).comap O.subtype = _root_.commutator ↥O
    rw [hΩO, ← Subgroup.map_subtype_commutator O]
    exact Subgroup.comap_map_eq_self_of_injective O.subtype_injective _
  haveI hN : ((StatedOmega (StatedQuadPlus m K)).subgroupOf O).Normal := by
    rw [hcomm]
    infer_instance
  have hsub : ((StatedOmega (StatedQuadPlus m K)).subgroupOf O).IsSubnormal := hN.isSubnormal
  have hle := CFSG.GH74.GLS.Balance.SolvComp.map_pCore_le_pCore_of_isSubnormal p hsub
  rw [hpO] at hle
  have hpΩsub : CFSG.pCore p ↥((StatedOmega (StatedQuadPlus m K)).subgroupOf O) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _
      ((StatedOmega (StatedQuadPlus m K)).subgroupOf O).subtype_injective).mp
      (le_bot_iff.mp hle)
  have h1 := CFSG.pCore_map_iso p (Subgroup.subgroupOfEquivOfLe hΩle)
  rw [hpΩsub, Subgroup.map_bot] at h1
  exact h1.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat
