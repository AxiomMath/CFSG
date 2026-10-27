module

public import CFSG.RankThree.PartOne.KE.Assembly
public import CFSG.RankThree.PartOne.KE.E7E8Families
public import CFSG.RankThree.PartOne.KE.CTWave1
public import CFSG.RankThree.PartOne.KE.CTWave1More
public import CFSG.RankThree.PartOne.KE.CTWaveTw
public import CFSG.RankThree.PartOne.KE.E7EightData
public import CFSG.RankThree.PartOne.KE.E7TwelveData
public import CFSG.RankThree.PartOne.KE.E7FourEndpoint
public import CFSG.RankThree.PartOne.KD4L.TranspositionLayer
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.E8EightPlane
public import CFSG.RankThree.PartOne.KE.E6FourFinal
public import CFSG.RankThree.PartOne.KE.E6TwFourFinal
public import CFSG.RankThree.PartOne.KE.E6TwThreeFinal
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.RankThree.PartOne.KE.TitsOddImage
public import CFSG.RankThree.PartOne.KGD.G2Family
public import CFSG.RankThree.PartOne.KE6.Phi3Final
public import CFSG.RankThree.PartOne.KE6.Phi6Final
public import CFSG.RankThree.PartOne.KE6.Tw6Final
public import CFSG.RankThree.PartOne.KE6.EqpFinal
public import CFSG.RankThree.PartOne.KE6.E8T3Final
public import CFSG.RankThree.PartOne.KE6.E6LLayer
public import CFSG.RankThree.PartOne.KE8F.HIPlane
public import CFSG.RankThree.PartOne.KE8F.PlaneFive
public import CFSG.RankThree.PartOne.KC1.Toral5
public import CFSG.RankThree.PartOne.KE.E7ThreeFinal
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer
public import CFSG.RankThree.PartOne.KGD.SmallRee
public import CFSG.RankThree.PartOne.KF4.F4ThreeEven
public import CFSG.RankThree.PartOne.KF4.F4FourEven
public import CFSG.RankThree.PartOne.KF4.QPlusData

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KETw3 (oddEndpoint_twE6_phi3)

theorem oddEndpoint_or {τ : CFSG.Assembly.LowTwoRank.StatedLieTag} {A B : ℕ → ℕ → ℕ → Prop} (hA : OddEndpoint τ A)
    (hB : OddEndpoint τ B) : OddEndpoint τ fun p ℓ f => A p ℓ f ∨ B p ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  rcases hc with hc | hc
  · exact hA G p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  · exact hB G p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL

structure F4OpenEndpoints : Prop

structure E6OpenEndpoints : Prop

structure E7OpenEndpoints : Prop where
  a5Layer : A5Layer .E7

structure E8OpenEndpoints : Prop

theorem f4Endpoints_of_open (_h : F4OpenEndpoints) : F4Endpoints where
  evenQPlus := CFSG.RankThree.PartOne.KF4.oddEndpoint_F4_evenQPlus
  evenPhi3 := CFSG.RankThree.PartOne.KF4.oddEndpoint_F4_evenPhi3
  evenPhi4 := CFSG.RankThree.PartOne.KF4.oddEndpoint_F4_evenPhi4
  evenPhi6 := CFSG.RankThree.PartOne.KF4.oddEndpoint_F4_evenPhi6
  oddPhi3Phi6 := CFSG.RankThree.PartOne.KF4.oddEndpoint_F4_oddPhi3Phi6
  oddPhi4 := CFSG.RankThree.PartOne.KF4.oddEndpoint_F4_oddPhi4
  phi8Phi12 := oddEndpoint_F4_phi8Phi12

theorem e6Endpoints_of_open (_h : E6OpenEndpoints) : E6Endpoints where
  evenQPlus := CFSG.RankThree.PartOne.KE6.oddEndpoint_E6_evenQPlus
  phi3 := CFSG.RankThree.PartOne.KE6.oddEndpoint_E6_phi3
  phi4 := oddEndpoint_E6_phi4
  phi6 := CFSG.RankThree.PartOne.KE6.oddEndpoint_E6_phi6
  phi8 := oddEndpoint_E6_phi8
  phi9 := oddEndpoint_E6_phi9
  phi12 := oddEndpoint_E6_phi12
  phi5 := oddEndpoint_E6_phi5
  twPhi3 := oddEndpoint_twE6_phi3
  twPhi4 := oddEndpoint_twE6_phi4
  twPhi6 := CFSG.RankThree.PartOne.KE6.oddEndpoint_twE6_phi6
  twPhi8 := oddEndpoint_twistedE6_phi8
  twPhi10 := oddEndpoint_twE6_phi10
  twPhi12 := oddEndpoint_twistedE6_phi12
  twPhi18 := oddEndpoint_twistedE6_phi18

theorem e7Endpoints_of_open (h : E7OpenEndpoints) : E7Endpoints where
  phi3Phi6 := oddEndpoint_E7_phi3Phi6 CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 h.a5Layer
  phi4Phi12 := oddEndpoint_or (oddEndpoint_E7_phi4 CFSG.RankThree.PartOne.KD4L.d4TranspositionLayer_E7)
    oddEndpoint_E7_phi12
  phi8 := oddEndpoint_E7_phi8
  coxeter := oddEndpoint_E7_coxeter
  phi5Phi10 := oddEndpoint_E7_phi5Phi10
  phi7Phi14 := oddEndpoint_E7_phi7Phi14

theorem oddEndpoint_E8_phi4_of_pieces
    (hBig : OddEndpoint .E8 fun p ℓ f => 5 < p ∧ (p : ℤ) ∣ cycloVal 4 ℓ f)
    (hTwo : OddEndpoint .E8 fun p ℓ f => p = 5 ∧ ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 4 ℓ f) :
    OddEndpoint .E8 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f ∧ (p = 5 → ℓ = 2) := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  obtain ⟨hc, h2⟩ := hc
  by_cases h5 : p = 5
  · exact hTwo G p ℓ f hp hp3 hℓ hℓp hf ⟨h5, h2 h5, hc⟩ E hE hEc t ht ht1 L hL hmod hEL hSL
  · have h6 : 5 < p := by
      by_contra hle
      have h4 : p = 4 := by omega
      subst h4
      exact absurd hp (by decide)
    exact hBig G p ℓ f hp hp3 hℓ hℓp hf ⟨h6, hc⟩ E hE hEc t ht ht1 L hL hmod hEL hSL

theorem e8Endpoints_of_open (_h : E8OpenEndpoints) (hTri : D4TrialityLayer .E8)
    (hTrans : D4TranspositionLayer .E8) : E8Endpoints where
  phi3Phi6 := CFSG.RankThree.PartOne.KE6.oddEndpoint_E8_phi3Phi6 hTri
    CFSG.RankThree.PartOne.KE6.e6Layer_E8
  phi4 := oddEndpoint_E8_phi4_of_pieces CFSG.RankThree.PartOne.KE8F.oddEndpoint_E8_phi4_big
    (CFSG.RankThree.PartOne.KE8F.oddEndpoint_E8_phi4_five CFSG.RankThree.PartOne.KC1.phi4FiveToral)
  phi8Phi12 := oddEndpoint_or (oddEndpoint_E8_phi8 hTrans) (oddEndpoint_E8_phi12 hTri)
  phi9Phi18 := oddEndpoint_E8_phi9Phi18
  phi15Phi30 := oddEndpoint_E8_phi15Phi30
  phi5Phi10 := oddEndpoint_E8_phi5Phi10
  phi7Phi14 := oddEndpoint_E8_phi7Phi14
  phi20Phi24 := oddEndpoint_E8_phi20Phi24

theorem original_exceptional_component_local_core_odd_action_of_open
    (hF4 : F4OpenEndpoints)
    (hE6 : E6OpenEndpoints) (hE7 : E7OpenEndpoints) (hE8 : E8OpenEndpoints)
    (hTri8 : D4TrialityLayer .E8) (hTrans8 : D4TranspositionLayer .E8)
    (hD4 : OriginalTrialityComponentLocalCoreOddAction)
    (hLR : LargeReeAllActorsActualComponentLocalCoreProductOddAction) :
    OriginalExceptionalComponentLocalCoreOddAction :=
  original_exceptional_component_local_core_odd_action_of_families
    CFSG.RankThree.PartOne.KGD.g2_family
    (f4Complete_of_endpoints (f4Endpoints_of_open hF4))
    (originalE6_of_endpoints (e6Endpoints_of_open hE6))
    (originalE7_of_cyclotomic_endpoints (e7Endpoints_of_open hE7))
    (originalE8_of_cyclotomic_endpoints (e8Endpoints_of_open hE8 hTri8 hTrans8))
    hD4 suzuki_normalized_component_local_core_product_odd_image
    CFSG.RankThree.PartOne.KGD.smallRee_family hLR
    tits_normalized_component_local_core_product_odd_image

end CFSG.RankThree.PartOne.KE
