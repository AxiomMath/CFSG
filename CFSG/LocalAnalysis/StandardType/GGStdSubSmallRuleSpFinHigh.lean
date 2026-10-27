module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinII
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.SpFin

open Module CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.TwoThree TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

theorem spFinCore_holds : SpFinCore := by
  intro K _ _ hK m hm Ã hÃ hcard hU x hx hx1
  classical
  have hKc : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  haveI := finite_statedSp_group (K := K) (m := m)
  haveI := finite_units_end (K := K) (V := Fin m ⊕ Fin m → K)
  obtain ⟨U, hU1, hU2, hUÃ⟩ := hU
  obtain ⟨T, hT0, hTiso, hTÃ, -⟩ := SmallRule.exists_isotropic_card_sq_le hK (spLin m K)
    spLin_injective (spForm m K) spForm_nondegenerate spForm_isAlt.isRefl
    (fun g v w => mem_sesqUnitaryGroup.mp (spLin_mem g) v w) hÃ hU1 hU2 hUÃ
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hordp : orderOf (proj m K x) = 3 := by
    rw [orderOf_injective (proj m K) (proj_injective_sp (f := 1) (by rw [hK, pow_one]) le_rfl
      (by omega)) x]
    exact hord
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := 1)
    (p := 3) Nat.prime_two le_rfl (by rw [hK, pow_one]) Nat.prime_three (by norm_num)
    (by norm_num) (by omega : 1 ≤ m) (proj m K x) hordp
  have blocks := hblocks x rfl hord
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hseven : spFixedDim x = 2 * s := hs
  by_cases hd : 4 ≤ spFixedDim x
  · exact coreI hK hm hÃ hcard hT0 hTiso hTÃ hx hx1 blocks hd
  · exact coreII hK hm hÃ hcard hT0 hTiso hTÃ hx hx1 blocks (by omega)

end CFSG.StandardType.SpFin

namespace CFSG.StandardType

theorem ggSpTwoNormSmallRHigh_holds :
    GGSpTwoNormSmallRHigh :=
  SpFin.ggSpTwoNormSmallRHigh_of_core SpFin.spFinCore_holds

end CFSG.StandardType
