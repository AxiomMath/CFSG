module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPLie

import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bA6

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem ff79KLemmaOP_holds (hExc : FF79KLemmaOExc) :
    FF79KLemmaOP := by
  intro L _ _ hs hna hcat hA3 hB x hx hout K hKle hA hKc _
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨idx, ⟨e⟩⟩ := hcat
  cases idx with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    refine hab (e.injective ?_)
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exfalso
    by_cases hn6 : n = 6
    · subst hn6
      obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.alt6_aut_three_inner
        (MulAut.congr e x) (by rw [← map_pow, hx3, map_one])
      refine hout (e.symm g) (MulEquiv.ext fun y => ?_)
      have := MulEquiv.congr_fun hg (e y)
      simpa using (congrArg e.symm this).symm
    · obtain ⟨g, hg⟩ := CFSG.ComponentClassification.FooteLit.AltCore.oddOuterInner_alternating
        hn hn6 e x (by rw [hx]; decide)
      exact hout g hg
  | sporadic name =>
    exfalso
    have hle := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds L hs hna name ⟨e⟩
    have h3d := LemmaOLin.three_dvd_card_outer_of_outer_order_three
      hx3 hout
    have := Nat.le_of_dvd Nat.card_pos h3d
    omega
  | lie d => exact lemmaO_lie_P hExc hs hna d ⟨e⟩ hA3 hB hx3 hout hKle hA hKc

end CFSG.RankThree.PartTwo.Sec21.FF79
