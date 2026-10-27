module

public import CFSG.LocalAnalysis.UniqueFourCatalog.TwistedE6OddCore
public import CFSG.LocalAnalysis.UniqueFourCatalog.TwistedOddInputs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvolutionLocal
public import CFSG.RankThree.PartTwo.Census.Criteria

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Bridge


theorem hasInvolutionComponent_graphFixedRootGroup_E6_odd
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    HasInvolutionComponent ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨s, P, hs1, hs2, hPs, hPperf, hP1⟩ :=
    exists_involution_perfect_centralizer TwistTag.E6 e6odd_exists_orbit hp hf hodd K hK σ hσ
  exact hasInvolutionComponent_of_perfect_centralizer_E6 hp hf hodd K hK σ hσ s P hs1 hs2 hPs
    hPperf hP1

theorem not_isCharTwoType_of_twistedE6Model_odd {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hodd : Odd (p ^ f)) {H : Type} [Group H] (h : TwistedChevalleyModel H .E6 (p ^ f)) :
    ¬ CFSG.Open.IsCharTwoType H := by
  obtain ⟨K, _, _, hK, σ₀, hσ₀, ⟨φ⟩⟩ := h
  intro hchar
  haveI := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  obtain ⟨σ, hσ, -, -, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hp hf K hK
  have hσeq : σ₀ = σ.toRingHom := RingHom.ext fun c => (hσ₀ c).trans (hσ c).symm
  subst hσeq
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (p ^ f) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 hp hf K hK σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hderived : Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
    have h1 := hperf.2.2.1
    unfold DerivedCentralQuotient
    rw [h1]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩
  obtain ⟨ψ⟩ := hderived
  let e : H ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := φ.trans ψ
  have hC : CFSG.Open.IsCharTwoType ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv e hchar
  haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := inferInstance
  exact CFSG.RankThreeEvenClassification.Helpers.charTwoType_no_involution_component hC
    (hasInvolutionComponent_graphFixedRootGroup_E6_odd hp hf hodd K hK σ hσ)

theorem twistedE6OddExclusion : TwistedE6OddExclusion := by
  intro G _ _ hS p f hp2 h
  obtain ⟨hadm, hmatch⟩ := h
  have hodd : Odd (p ^ f) := (hadm.1.odd_of_ne_two hp2).pow
  exact not_isCharTwoType_of_twistedE6Model_odd hadm.1 hadm.2.1 hodd hmatch hS.charTwo

end Bridge

end CFSG.LocalAnalysis.UniqueFourCatalog
