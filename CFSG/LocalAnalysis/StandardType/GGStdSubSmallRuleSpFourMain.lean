module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourD4
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.SpFour

open Module Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

theorem spFourCore_holds : SpFourCore := by
  intro K _ _ hK Ã hÃ hcard hU x hx hx1 hEN hRule
  classical
  have hKc : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  haveI := SpFin.finite_statedSp_group (K := K) (m := 4)
  haveI := finite_units_end (K := K) (V := Fin 4 ⊕ Fin 4 → K)
  obtain ⟨U, hU1, hU2, hUÃ⟩ := hU
  obtain ⟨T, hT0, hTiso, hTÃ, -⟩ := SmallRule.exists_isotropic_card_sq_le hK (spLin 4 K)
    spLin_injective (spForm 4 K) spForm_nondegenerate spForm_isAlt.isRefl
    (fun g v w => mem_sesqUnitaryGroup.mp (spLin_mem g) v w) hÃ hU1 hU2 hUÃ
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  have hx3' : spLin 4 K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx1' : spLin 4 K x ≠ 1 := fun h => hx1 (spLin_injective (h.trans (map_one _).symm))
  have blocks := blocks_of_order_three hK (by norm_num) hx3 hx1
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) +
      finrank K (LinearMap.range (spEnd x - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hx3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  have hrng : 1 ≤ finrank K (LinearMap.range (spEnd x - 1)) :=
    Submodule.one_le_finrank_iff.mpr (SpFin.rng_ne_bot hx1')
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hseven : spFixedDim x = 2 * s := hs
  have hcases : spFixedDim x = 0 ∨ spFixedDim x = 2 ∨ spFixedDim x = 4 ∨ spFixedDim x = 6 := by
    omega
  rcases hcases with h | h | h | h
  · exact conclAt_of_zero hK hÃ hcard hT0 hTiso hTÃ hx hx1 blocks h hEN
  · exact (not_isComponentOf_of_two hK hx3 hx1 blocks h hEN.1).elim
  · exact (false_of_four hK hÃ hcard hT0 hTiso hTÃ hx hx1 blocks h hEN hRule).elim
  · exact conclAt_of_six hK hÃ hcard hT0 hTiso hTÃ hx hx1 blocks h hEN

end CFSG.StandardType.SpFour

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSpTwoNormSmallRFour_holds :
    GGSpTwoNormSmallRFour :=
  SpFour.ggSpTwoNormSmallRFour_of_core SpFour.spFourCore_holds

end CFSG.StandardType
