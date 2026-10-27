module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.StandardType.KGCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem entrywise_eq_one_of_conj_pinnedElt
    {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {σ : K ≃+* K} {g : adjointGroup τ K}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hβp : 0 < height β)
    (hg : ∀ c : K, g * SeitzReduction.EPilot.pinnedElt τ β (σ c) * g⁻¹ =
      SeitzReduction.EPilot.pinnedElt τ β c) :
    σ = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨w, hw⟩ := SeitzReduction.EPilot.exists_smul_eq_highRoot_of_pos hτ hβ hβp
  set n := canonicalRep (coxeterSystem τ) K w with hn_def
  have hn : ∀ c, n * pinnedX τ K β c * n⁻¹ = pinnedX τ K (SeitzReduction.highRoot τ) c :=
    fun c => by rw [hn_def, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hβ c, hw]
  have hg' : ∀ c, n * g * n⁻¹ * pinnedX τ K (SeitzReduction.highRoot τ) (σ c) *
      (n * g * n⁻¹)⁻¹ = pinnedX τ K (SeitzReduction.highRoot τ) c := by
    intro c
    have h : (g : ModGL τ K) * pinnedX τ K β (σ c) * (g : ModGL τ K)⁻¹ = pinnedX τ K β c :=
      congrArg Subtype.val (hg c)
    rw [← hn (σ c), ← hn c, ← h]
    group
  have hgC : n * g * n⁻¹ ∈ adjointGroup τ K :=
    mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K w) g.2)
      (inv_mem (canonicalRep_mem_adjointGroup _ K w))
  have h1 : n * g * n⁻¹ ∈ Subgroup.centralizer
      ({pinnedX τ K (SeitzReduction.highRoot τ) 1} : Set (ModGL τ K)) ⊓ adjointGroup τ K := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hgC⟩
    have e := hg' 1
    rw [map_one] at e
    exact mul_inv_eq_iff_eq_mul.1 e
  refine RingEquiv.ext fun c => ?_
  show σ c = c
  by_cases hc : c = 0
  · rw [hc, map_zero]
  have hσc : σ c ≠ 0 := (map_ne_zero σ).2 hc
  rw [SeitzReduction.EPilot.centralizer_pinnedX_highRoot_inf_eq hτ one_ne_zero,
    ← SeitzReduction.EPilot.centralizer_pinnedX_highRoot_inf_eq hτ hσc] at h1
  have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).1
  have e := hg' c
  rw [hcomm, mul_inv_cancel_right] at e
  exact pinnedX_injective τ K _ e

end CFSG.StandardType.KGCentExc

end
