module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRank
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem mem_inner_of_mem_sup_centOverO2 {M X : Subgroup G} (hXM : X ≤ M)
    (hMN : M ≤ normalizer (X : Set G)) {m : ↥M}
    (hm : (m : G) ∈ X ⊔ F08.CentOverO2 M X) :
    (rhoL X).comp (Subgroup.inclusion hMN) m ∈ Inn (Bar2 X) := by
  classical
  let C : Subgroup G := F08.CentOverO2 M X
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  have hCM : C ≤ M := fun x hx => (mem_centOverO2_iff.mp hx).1
  have hker : C.subgroupOf M = ρ.ker := by
    rw [← Subgroup.comap_subtype]
    change (F08.CentOverO2 M X).comap M.subtype = ρ.ker
    rw [centOverO2_eq_ker_map hMN]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hle : (X ⊔ C).subgroupOf M ≤ (Inn (Bar2 X)).comap ρ := by
    rw [Subgroup.subgroupOf_sup hXM hCM]
    refine sup_le (fun x hx => ?_) (fun c hc => ?_)
    · have hxX : (x : G) ∈ X := hx
      have heq : (⟨(x : G), hMN x.2⟩ : ↥(normalizer (X : Set G))) =
          ⟨(x : G), Subgroup.le_normalizer hxX⟩ := Subtype.ext rfl
      show ρ x ∈ Inn (Bar2 X)
      rw [show ρ x = rhoL X ⟨(x : G), hMN x.2⟩ from rfl, heq,
        rhoL_inner X (x : G) hxX]
      exact ⟨_, rfl⟩
    · have hcC : (c : G) ∈ C := hc
      have hker' : c ∈ ρ.ker := by
        rw [← hker]
        exact Subgroup.mem_subgroupOf.mpr hcC
      show ρ c ∈ Inn (Bar2 X)
      rw [MonoidHom.mem_ker.mp hker']
      exact Subgroup.one_mem _
  exact hle (Subgroup.mem_subgroupOf.mpr hm)

theorem mem_sup_centOverO2_of_mem_inner {M X : Subgroup G} (hXM : X ≤ M)
    (hMN : M ≤ normalizer (X : Set G)) {m : ↥M}
    (hm : (rhoL X).comp (Subgroup.inclusion hMN) m ∈ Inn (Bar2 X)) :
    (m : G) ∈ X ⊔ F08.CentOverO2 M X := by
  classical
  let C : Subgroup G := F08.CentOverO2 M X
  let ρ : ↥M →* MulAut (Bar2 X) := (rhoL X).comp (Subgroup.inclusion hMN)
  obtain ⟨h, hh⟩ := hm
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) h
  have hxX : (x : G) ∈ X := x.2
  have hx' : QuotientGroup.mk (⟨(x : G), hxX⟩ : ↥X) = h := by
    simpa using hx
  have hρx : ρ ⟨(x : G), hXM hxX⟩ = MulAut.conj h := by
    rw [show ρ ⟨(x : G), hXM hxX⟩ = rhoL X ⟨(x : G), hMN (hXM hxX)⟩ from rfl,
      show (⟨(x : G), hMN (hXM hxX)⟩ : ↥(normalizer (X : Set G))) =
        ⟨(x : G), Subgroup.le_normalizer hxX⟩ from Subtype.ext rfl,
      rhoL_inner X (x : G) hxX, hx']
  have hmemker : m * (⟨(x : G), hXM hxX⟩ : ↥M)⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρx, hh, mul_inv_cancel]
  have hCmem : (m : G) * (x : G)⁻¹ ∈ C := by
    change (m : G) * (x : G)⁻¹ ∈ F08.CentOverO2 M X
    rw [centOverO2_eq_ker_map hMN]
    exact Subgroup.mem_map_of_mem M.subtype hmemker
  have hmul : (m : G) = ((m : G) * (x : G)⁻¹) * (x : G) := by group
  rw [hmul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hCmem) (Subgroup.mem_sup_left hxX)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
