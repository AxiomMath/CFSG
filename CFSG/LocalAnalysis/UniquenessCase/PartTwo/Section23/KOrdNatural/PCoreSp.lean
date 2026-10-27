module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.PCore.Construction
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
import CFSG.CGT.Timmesfeld75.Forms
import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.ClassicalGroups.Symplectic.StatedSpTransport
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.RankThree.GF2n.Stroth80.Anisotropic
import CFSG.RankThree.GF2n.Stroth80.FrobClause
import CFSG.RankThree.GF2n.Stroth80.GlobalModel
import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec41
import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open

private noncomputable def spNatRep (m : ℕ) (K : Type) [Field K] :
    Representation K ↥(StatedSp m K) (Fin m ⊕ Fin m → K) where
  toFun g := Matrix.mulVecLin
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

private theorem spNatRep_injective (m : ℕ) (K : Type) [Field K] :
    Function.Injective (spNatRep m K) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply Matrix.mulVec_injective
  funext v
  have := LinearMap.congr_fun hgh v
  simpa [spNatRep, Matrix.mulVecLin_apply] using this

private theorem spNatRep_isIrreducible (m : ℕ) (K : Type) [Field K] (hm : 0 < m) :
    (spNatRep m K).IsIrreducible := by
  haveI : Nontrivial (Fin m ⊕ Fin m → K) :=
    ⟨0, Pi.single (Sum.inl ⟨0, hm⟩) 1, fun hconv => by
      have h := congrFun hconv (Sum.inl ⟨0, hm⟩)
      simp only [Pi.zero_apply, Pi.single_eq_same] at h
      exact zero_ne_one h⟩
  haveI : Nontrivial (Subrepresentation (spNatRep m K)) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule K (Fin m ⊕ Fin m → K))
      (congrArg Subrepresentation.toSubmodule h)⟩
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hWne
  have hWsub : W.toSubmodule = ⊥ ∨ W.toSubmodule = ⊤ := by
    refine CFSG.RankThree.GF2n.Stroth80.natIrred_statedSp (K := K) (m := m) W.toSubmodule ?_
    intro g hg v hv
    have := W.apply_mem_toSubmodule ⟨g, hg⟩ hv
    simpa [spNatRep, Matrix.mulVecLin_apply] using this
  rcases hWsub with h | h
  · exact absurd (Subrepresentation.toSubmodule_injective (by rw [h]; rfl)) hWne
  · exact Subrepresentation.toSubmodule_injective (by rw [h]; rfl)

theorem pCore_statedSp_eq_bot {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (m : ℕ) : CFSG.pCore p ↥(StatedSp m K) = ⊥ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : Subsingleton ↥(StatedSp 0 K) := inferInstance
    rw [eq_bot_iff]
    intro x _
    exact Subsingleton.elim x 1
  · exact CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible
      p (spNatRep m K) (spNatRep_injective m K) (spNatRep_isIrreducible m K hm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat
