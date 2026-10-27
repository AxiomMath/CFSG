module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Polynomial Module CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem fixedDim_ge_four_of_quasisimple_derived_fixed
    (hK : Nat.card K = 2) (hn : 1 ≤ n) {t : StatedSp n K} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported t {X - 1}, spSupported t {X - 1}⁆) :
    4 ≤ spFixedDim t := by
  have blocks := CFSG.LocalAnalysis.GLTheoremA.T173O.spPrimaryBlocks_of_order_three hK hn ht3 ht1
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hd : spFixedDim t = 2 * s := hs
  by_contra h
  have hcases : spFixedDim t = 0 ∨ spFixedDim t = 2 := by omega
  rcases hcases with h0 | h2
  · have hsol : Group.IsSolvable ↥(spSupported t {X - 1}) := by
      change Group.IsSolvable ↥(spFixedFactor t)
      rw [CFSG.LocalAnalysis.GLTheoremA.T173O.spFixedFactor_eq_bot_of_spFixedDim_eq_zero ht3 h0]
      infer_instance
    exact SpFour.not_isQuasisimple_commutator_of_solvable hsol hQ
  · have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd t) := by
      by_contra hnot
      have hbot := primaryComponent_eq_bot_of_not_mem
        (irreducible_X_sub_one (K := K)) (monic_X_sub_one (K := K)) hnot
      change finrank K (primaryComponent (spEnd t) (X - 1)) = 2 at h2
      rw [hbot, finrank_bot] at h2
      omega
    exact SpFour.not_isQuasisimple_commutator_of_solvable
      (SpFour.fixedFactor_solvable_of_two hK blocks hmem h2) hQ

theorem movingMultiplicity_ge_four_of_quasisimple_derived
    (hK : Nat.card K = 2) (hn : 1 ≤ n) {t : StatedSp n K} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported t {X ^ 2 + X + 1},
      spSupported t {X ^ 2 + X + 1}⁆) :
    4 ≤ primaryMultiplicity (spEnd t) (X ^ 2 + X + 1) := by
  have blocks := CFSG.LocalAnalysis.GLTheoremA.T173O.spPrimaryBlocks_of_order_three hK hn ht3 ht1
  have hmem := SpFin.h3_mem_primaryFactors hK ht3 ht1
  have h3K : (3 : K) ≠ 0 := by
    intro hz
    have hdiv := (CharP.cast_eq_zero_iff K 2 3).mp hz
    norm_num at hdiv
  have hsq : Squarefree (minpoly K (spEnd t)) := (altPrimaryData_spLin h3K ht3).squarefree
  have hpos : 1 ≤ primaryMultiplicity (spEnd t) (SpFin.h3 K) :=
    CFSG.RankThree.PartOne.KCUnitaryModel.primaryMultiplicity_pos hsq ⟨SpFin.h3 K, hmem⟩
  change 4 ≤ primaryMultiplicity (spEnd t) (SpFin.h3 K)
  change CFSG.IsQuasisimple ↥⁅spSupported t {SpFin.h3 K}, spSupported t {SpFin.h3 K}⁆ at hQ
  by_contra h
  have hsmall : primaryMultiplicity (spEnd t) (SpFin.h3 K) ≤ 3 := by omega
  exact SpFour.not_isQuasisimple_commutator_of_solvable
    (SpFour.selfDual_solvable_of_le hK blocks hmem hsmall hpos) hQ

end CFSG.StandardType.QTwoSymplecticCav

end
