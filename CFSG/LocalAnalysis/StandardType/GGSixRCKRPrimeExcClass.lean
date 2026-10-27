module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClassShape
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRankFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloorsAll
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcEigen
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.SeitzGeneration CFSG.StandardType.ExcMaxToral CFSG.RankThree.E6
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag IsElemAbelian)
open scoped Matrix

theorem rckExcClassAt_holds :
    RCKExcClassAt (fun t => t = .F4 ∨ t = .E7 ∨ t = .E8) := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ θ A' hframe htoral Dl ρ hΦ hρ hA'
  have hcfg := h
  unfold RCKRPConfig at hcfg
  obtain ⟨hGG, -, hp, hp2, -, hB1A, -, -, -, -, -, -, hp4, -, -, -⟩ := hcfg
  have hf : 1 ≤ f := hGG.1.1.2.1
  obtain ⟨-, -, hA'le, hA'el, hA'card, -, -⟩ := hframe
  have hBA : p ^ 4 ≤ Nat.card A := hp4.trans (Subgroup.card_le_of_le hB1A)
  have hp4A : p ^ 4 ≤ Nat.card A' := by
    rw [hA'card]
    exact hBA
  have htw : t ≠ .twistedE6 := by
    rcases ht with rfl | rfl | rfl <;> decide
  obtain ⟨w, hw, hcard⟩ := rckExc_torus_eigen_untwisted htw hf hp hp2 Dl ρ hΦ hρ A' hA'el hA'
  have hdeg := rckExcRankFour_holds t ht f hf p hp hp2 A' hA'le hA'el hp4A
  have hτ : langTag t = .F4 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl <;> simp [langTag]
  refine rckExcClassShape_of_weyl hτ hp hp2 hw hcard ?_ ?_ ?_ hp4A hdeg
  · intro hd1
    rw [hA'card]
    rcases ht with rfl | rfl | rfl
    · exact hBA
    · exact rckExc_E7_floor_split h (rck_dvd_of_orderOf_one hd1)
    · exact rckExc_E8_floor_split h (rck_dvd_of_orderOf_one hd1)
  · intro hd2
    rw [hA'card]
    rcases ht with rfl | rfl | rfl
    · exact (Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)).trans hBA
    · exact rckExc_E7_floor_half h (rck_dvd_of_orderOf_two hp hd2)
    · exact rckExc_E8_floor_half h (rck_dvd_of_orderOf_two hp hd2)
  · intro hF
    rw [hA'card]
    rcases ht with rfl | rfl | rfl
    · exact hBA
    · exact absurd hF (by decide)
    · exact absurd hF (by decide)

end CFSG.StandardType.RCKRP
