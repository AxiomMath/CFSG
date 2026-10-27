module

public import CFSG.Quasithin.H13.NQCatCartanSp4
public import CFSG.Quasithin.H13.NQCatCartanL3
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111Rk2

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem factRank2CartanGraph_holds : FactRank2CartanGraph := by
  intro Y _ _ k hk h U hU α hα hαU hN
  rcases h with (hL | ⟨F, _, _, hcard, ⟨e⟩⟩) | hSp
  · obtain ⟨K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
    refine ((cartanConcl_of_sylow (CartanL3.cartanConcl_projectiveSL hk hcard) hU₀ e.symm
      hU).mono fun h4 => ?_) α hα hαU hN
    have hk2 : k = 2 := Nat.pow_right_injective le_rfl (by rw [← hcard, h4]; rfl : 2 ^ k = 2 ^ 2)
    subst hk2
    exact hL
  · have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
    have hU₀ : IsSylowTwoOf (unitriangular 3 F) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact ((cartanConcl_of_sylow (CartanL3.cartanConcl_specialLinear hk hcard) hU₀ e.symm
      hU).mono False.elim) α hα hαU hN
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hSp
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    obtain ⟨Q, hQ⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
    have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
    exact ((cartanConcl_of_sylow
      (CartanSp4.cartanConcl_projSp (exists_finset_card_four_of_card hk hcard)) hU₀ e.symm
      hU).mono False.elim) α hα hαU hN

end CFSG.Quasithin.H13.NQCat
