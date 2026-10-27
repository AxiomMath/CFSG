module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndB
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem not_three_dvd_card_outer_psu3 :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Open.PSU3 3 1)) := by
  have hX : Nat.card (CFSG.Open.PSU3 3 1) = 6048 :=
    CFSG.Quasithin.H13.Sec526.card_psu3_three_one
  haveI : Finite (CFSG.Open.PSU3 3 1) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  haveI hsimple : IsSimpleGroup (CFSG.Open.PSU3 3 1) := by
    obtain ⟨e⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
    exact e.isSimpleGroup_congr.mp CFSG.Quasithin.isSimpleGroup_u33Pres
  refine CFSG.Quasithin.H13.S126C.not_three_dvd_card_outer_of_le ?_ ?_
  · exact CFSG.Quasithin.H13.S126C.center_eq_bot_of_simple_of_not_prime
      (by rw [hX]; norm_num)
  · rw [hX]
    have hle := CFSG.Quasithin.card_mulAut_psu3_le
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
