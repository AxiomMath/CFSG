module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankFamilies
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcTwistedOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)

section Griess

theorem k_CartanRank_twistedE6_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRank_twistedE6 := by
  change K_CartanRankFamily .twistedE6
  intro K _ _ m f hadm hmodel hq hodd S hS r hr hr2 hrdvd _ _
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  have hm0 : m = 0 := hadm.2.2
  rw [hm0] at hmodel ⊢
  have hdiv := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodel
  have hgen1 : (CFSG.Blueprint.Multiplier.genericOrders .twistedE6 0 2 f).1 = Nat.gcd 3 (2 ^ f + 1) :=
    rfl
  have hgen2 : (CFSG.Blueprint.Multiplier.genericOrders .twistedE6 0 2 f).2 = 1 := rfl
  rw [hgen1, hgen2, mul_one] at hdiv
  have hcop : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hd
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
      ((hd.trans hdiv).trans (Nat.gcd_dvd_left _ _))
    have hplus : r ∣ 2 ^ f + 1 := (hd.trans hdiv).trans (Nat.gcd_dvd_right _ _)
    subst hr3
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    generalize 2 ^ f = x at hplus hrdvd h1
    omega
  have hW := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_borelWit_of_central_quotient
    (Z := Subgroup.center K) le_rfl hr hcop
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_twE6_borelWit_orbit hmodel hr hrdvd)
  exact cartanRank_le_of_borelWit rfl hW hr hr2 S hS

end Griess

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
