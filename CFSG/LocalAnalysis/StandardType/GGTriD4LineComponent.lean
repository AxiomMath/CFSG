module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalANormal
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

private lemma triD4Line_commutatorElement_prod {M N : Type*} [Group M] [Group N]
    (a₁ a₂ : M) (b₁ b₂ : N) :
    ⁅(a₁, b₁), (a₂, b₂)⁆ = (⁅a₁, a₂⁆, ⁅b₁, b₂⁆) := by
  rw [commutatorElement_def, commutatorElement_def]
  rfl

private lemma triD4Line_commutator_mem_N0 (k K : Type) [Field k] [Field K] [Algebra k K]
    (x y : TriD4LineX k K) : ⁅x, y⁆ ∈ triD4LineN0 k K := by
  obtain ⟨g, c, h, rfl⟩ := triD4LineMk_surjective k K x
  obtain ⟨g', c', h', rfl⟩ := triD4LineMk_surjective k K y
  let a : triD4LineFibre k K := ⟨(g, c), h⟩
  let b : triD4LineFibre k K := ⟨(g', c'), h'⟩
  have ha : triD4LineMk k K g c h = QuotientGroup.mk' (triD4LineDiag k K) a := rfl
  have hb : triD4LineMk k K g' c' h' = QuotientGroup.mk' (triD4LineDiag k K) b := rfl
  rw [ha, hb, ← map_commutatorElement]
  have hcomm : ((⁅a, b⁆ : triD4LineFibre k K) : GL (Fin 3) k × Kˣ) = (⁅g, g'⁆, 1) := by
    have h1 : ((⁅a, b⁆ : triD4LineFibre k K) : GL (Fin 3) k × Kˣ) =
        ⁅(a : GL (Fin 3) k × Kˣ), (b : GL (Fin 3) k × Kˣ)⁆ :=
      map_commutatorElement (Subgroup.subtype (triD4LineFibre k K)) a b
    rw [h1]
    have hca : (a : GL (Fin 3) k × Kˣ) = (g, c) := rfl
    have hcb : (b : GL (Fin 3) k × Kˣ) = (g', c') := rfl
    rw [hca, hcb, triD4Line_commutatorElement_prod]
    have hcc : ⁅c, c'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (mul_comm c c')
    simp only [hcc, Prod.mk.injEq, true_and]
  have hdet : Matrix.GeneralLinearGroup.det ⁅g, g'⁆ =
      Units.map (Algebra.norm k (S := K)) 1 := by
    have hmem := (⁅a, b⁆ : triD4LineFibre k K).2
    rw [hcomm] at hmem
    exact hmem
  have hab : ⁅a, b⁆ = ⟨(⁅g, g'⁆, 1), hdet⟩ := Subtype.ext hcomm
  rw [hab]
  exact (mem_triD4LineN0_iff k K _).2 ⟨⁅g, g'⁆, hdet, rfl⟩

private lemma triD4Line_commutator_le_N0 (k K : Type) [Field k] [Field K] [Algebra k K] :
    ⁅(⊤ : Subgroup (TriD4LineX k K)), ⊤⁆ ≤ triD4LineN0 k K :=
  Subgroup.commutator_le.2 fun x _ y _ => triD4Line_commutator_mem_N0 k K x y

private lemma triD4Line_N0_quasisimple (k K : Type) [Field k] [Field K] [Algebra k K] :
    Assembly.IsQuasisimple ↥(triD4LineN0 k K) := by
  have hSL3 : Assembly.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) k) := by
    have h := CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (n := 3) (K := k)
      (by norm_num)
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  let e : Matrix.SpecialLinearGroup (Fin 3) k ≃* ↥(triD4LineN0 k K) :=
    (MonoidHom.ofInjective (triD4LineSL3_injective k K)).trans
      (MulEquiv.subgroupCongr (triD4LineSL3_range k K))
  exact Assembly.IsQuasisimple.of_mulEquiv e.symm hSL3

private lemma triD4Line_perfect_of_isQuasisimple {X : Type*} [Group X] {J : Subgroup X}
    (h : Assembly.IsQuasisimple ↥J) : ⁅J, J⁆ = J := by
  have hmap : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
    unfold commutator
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have htop : (commutator ↥J).map J.subtype = J := by
    rw [h.1, Subgroup.map_top, Subgroup.range_subtype]
  rwa [hmap] at htop

theorem triD4LineN0_unique_component (k K : Type) [Field k] [Field K] [Algebra k K] :
    ∀ J : Subgroup (TriD4LineX k K), IsComponentOf J ⊤ ↔ J = triD4LineN0 k K := by
  have hN0q : Assembly.IsQuasisimple ↥(triD4LineN0 k K) := triD4Line_N0_quasisimple k K
  have hcomm : ⁅(⊤ : Subgroup (TriD4LineX k K)), ⊤⁆ ≤ triD4LineN0 k K :=
    triD4Line_commutator_le_N0 k K
  refine fun J => ⟨fun hJ => ?_, fun hJ => ?_⟩
  · have hJq : Assembly.IsQuasisimple ↥J := hJ.2.2
    have hJperf : ⁅J, J⁆ = J := triD4Line_perfect_of_isQuasisimple hJq
    have hJne : J ≠ ⊥ := by
      have hnt : Nontrivial ↥J := by
        haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJq.2.toNontrivial
        exact (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot J).1 hnt
    have hJN : J ≤ triD4LineN0 k K := by
      rw [← hJperf]
      exact (Subgroup.commutator_mono le_top le_top).trans hcomm
    have hsubOpen : CFSG.Open.IsSubnormal J ⊤ := CFSG.Assembly.isSubnormal_iff_open.1 hJ.2.1
    have hsubN : CFSG.Open.IsSubnormal J (triD4LineN0 k K) := by
      have := CFSG.Open.IsSubnormal.inf_of_le hsubOpen (le_top : triD4LineN0 k K ≤ ⊤)
      rwa [inf_eq_left.2 hJN] at this
    exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.eq_of_perfect_subnormal_of_quasisimple
      hN0q hJN hsubN hJperf hJne
  · rw [hJ]
    exact ⟨le_top, Assembly.IsSubnormal.of_mathlib (triD4LineN0_normal k K).isSubnormal, hN0q⟩

end CFSG.StandardType
