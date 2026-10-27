module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6Adj
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongLift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedE6
  CFSG.SeitzReduction CFSG.SeitzReduction.F4Pilot
open scoped commutatorElement

theorem map_twistedIsogenyC_rootGroup_highRoot
    {f : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2] (hf : 1 ≤ f) (hK : Nat.card k = (2 ^ f) ^ 2)
    (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f)) :
    ((twistedDatum k θ).rootGroup (highRoot .F4)).map (twistedIsogenyC hf hK θ hσ) =
      (rootSubgroup TwistTag.E6.tag k e6HighestRoot).comap
        (graphFixedRootGroup TwistTag.E6 k θ).subtype := by
  have hp : proj (highRoot .E6) = highRoot .F4 := by decide +kernel
  have hfix : rho (highRoot .E6) = highRoot .E6 := by
    show permLattice TwistTag.E6.perm (highRoot .E6) = highRoot .E6
    exact permLattice_e6HighestRoot
  have hα : IsRoot .E6 (highRoot .E6) := isRoot_highRoot .E6
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_comap]
    obtain ⟨c, hc, hxval⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα hp hfix x).1 hx
    change ((twistedIsogenyC hf hK θ hσ x : graphFixedRootGroup TwistTag.E6 k θ) :
      ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot
    rw [coe_twistedIsogenyC]
    rw [hxval]
    exact mem_rootSubgroup.2 ⟨c, (CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hα c).symm⟩
  · rintro y hy
    rw [Subgroup.mem_comap] at hy
    change (y : ModGL TwistTag.E6.tag k) ∈ rootSubgroup TwistTag.E6.tag k e6HighestRoot at hy
    obtain ⟨c, hc_eq⟩ := mem_rootSubgroup.1 hy
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have hyG : (y : ModGL TwistTag.E6.tag k) ∈ graphFixedRootGroup TwistTag.E6 k θ := y.2
    have hyF : (y : ModGL TwistTag.E6.tag k) ∈ CFSG.Blueprint.twistedFixedGroup .E6 k θ :=
      graphFixedRootGroup_le .E6 k θ hyG
    have htw : twistHom .E6 k θ (y : ModGL TwistTag.E6.tag k) =
        (y : ModGL TwistTag.E6.tag k) :=
      ((mem_twistedFixedGroup_iff_twistHom .E6 k θ).1 hyF).2
    have hαT : IsRoot TwistTag.E6.tag e6HighestRoot := isRoot_e6HighestRoot
    have htwp : pinnedX TwistTag.E6.tag k e6HighestRoot (θ c) =
        pinnedX TwistTag.E6.tag k e6HighestRoot c := by
      have h := CFSG.LieType.Chevalley.E6GraphRadical.twistHom_pinnedX_of_two h2 θ hαT c
      rw [permLattice_e6HighestRoot] at h
      rw [hc_eq, htw] at h
      exact h.symm.trans hc_eq.symm
    have hc : θ c = c := pinnedX_injective TwistTag.E6.tag k e6HighestRoot htwp
    refine ⟨xFixed θ hα hfix c hc, ?_, ?_⟩
    · exact (mem_twistedRootGroup_iff_of_fixed θ hα hp hfix _).2 ⟨c, hc, rfl⟩
    · apply Subtype.ext
      rw [coe_twistedIsogenyC]
      rw [xFixed_val θ hα hfix c hc]
      exact (CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hα c).trans hc_eq

theorem coreFour_twistedE6_highest
    {f : ℕ} {k : Type} [Field k] [Finite k] [CharP k 2] (hf : 1 ≤ f)
    (hK : Nat.card k = (2 ^ f) ^ 2) (θ : k →+* k) (hσ : ∀ c, θ c = c ^ (2 ^ f))
    (hodd : Odd (Nat.card (twistedIsogenyC hf hK θ hσ).ker)) :
    ⁅pCoreOf 2 (Subgroup.normalizer (((twistedDatum k θ).rootGroup (highRoot .F4) :
        Subgroup ↥(fixedGroup k θ)) : Set ↥(fixedGroup k θ))),
      pCoreOf 2 (Subgroup.normalizer (((twistedDatum k θ).rootGroup (highRoot .F4) :
        Subgroup ↥(fixedGroup k θ)) : Set ↥(fixedGroup k θ)))⁆ ≤
        (twistedDatum k θ).rootGroup (highRoot .F4) ∧
      pCoreOf 2 (Subgroup.normalizer (((twistedDatum k θ).rootGroup (highRoot .F4) :
        Subgroup ↥(fixedGroup k θ)) : Set ↥(fixedGroup k θ))) ≤
        Subgroup.centralizer (((twistedDatum k θ).rootGroup (highRoot .F4) :
          Subgroup ↥(fixedGroup k θ)) : Set ↥(fixedGroup k θ)) := by
  have hγ : highRoot .F4 ∈ (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]; exact isRoot_highRoot .F4
  haveI : Finite (graphFixedRootGroup TwistTag.E6 k θ) := inferInstance
  have hmap := map_twistedIsogenyC_rootGroup_highRoot hf hK θ hσ
  have hadj := coreFour_adjoint_twE6_highest θ
  refine CFSG.StandardType.LieKnownR2.four_lift_of_odd_central_ker
    (twistedIsogenyC_surjective hf hK θ hσ) (ker_twistedIsogenyC hf hK θ hσ).le hodd
    (isPGroup_two_twistedRootGroup θ hγ) ?_ ?_
  · rw [hmap]; exact hadj.1
  · rw [hmap]; exact hadj.2

end CFSG.StandardType.LieKnownR2.Short
