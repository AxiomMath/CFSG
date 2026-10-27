module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourHolds
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClass
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClassE6
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcEigen

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open (StatedLieTag)

theorem rckExcOrbitAt_holds :
    RCKExcOrbitAt (fun t => t = .F4 ∨ t = .E7 ∨ t = .E8) :=
  rckExcOrbitAt_of_four (fun _ _ Dl hΦ => rckExc_langDatum_q_eq Dl hΦ)
    (rckExcOrbitFour_of_shape rckExcShapeFour_holds)

theorem rckExcRelOneAt_F4E7E8 :
    RCKExcRelOneAt (fun t => t = .F4 ∨ t = .E7 ∨ t = .E8) :=
  rckExcRelOneAt_of_class_orbit rckExcClassAt_holds rckExcOrbitAt_holds

theorem rckExcRelOneAt_five :
    RCKExcRelOneAt CFSG.StandardType.GGExcFive := by
  have h := rckExcRelOne_of_split rckExcRelOneAt_F4E7E8 rckExcRelOneAt_E6_twE6
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht
  refine h X t n f ψ p G₀ A B₁ D J L R Rm K e ?_
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr rfl)

end CFSG.StandardType.RCKRP
