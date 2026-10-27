module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerSU33
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs

public section

namespace CFSG.StandardType

open CFSG.Sporadic.Schreier.Tits

theorem LayerCyc.eq_five_or_thirteen_of_prime_dvd_titsCard {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h3 : 3 < ℓ) (hdvd : ℓ ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13) : ℓ = 5 ∨ ℓ = 13 := by
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h)
        omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).mp (hℓ.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h)

theorem ggTitsThreeCentInput_holds :
    GGTitsThreeCentInput := by
  intro g x hg hxp hx3
  have hdvd : orderOf x ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by
    have := orderOf_dvd_natCard x
    rwa [card_titsD, show (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 by norm_num] at this
  exact CFSG.RankThree.PartTwo.Sec4.Item434RemTits.mul_ne_mul_of_orderOf hg
    (LayerCyc.eq_five_or_thirteen_of_prime_dvd_titsCard hxp hx3 hdvd) rfl

section Wiring

theorem ggLayerDerivedFixSolvableInput_holds : GGLayerDerivedFixSolvableInput :=
  ggLayerDerivedFixSolvableInput_of_tits ggTitsThreeCentInput_holds

theorem ggLayerCenterCyclicInput_of_exc
    (hexc : GGLayerCenterCyclicExcInput) : GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_tits_exc ggTitsThreeCentInput_holds hexc

end Wiring

end CFSG.StandardType

end
