module

public import CFSG.RankThree.PartOne.KLC.Descent
public import CFSG.RankThree.PartOne.KLC.EigE8
public import CFSG.RankThree.PartOne.KE.CTCasesE8Coxeter
public import CFSG.RankThree.PartOne.KE.CTCasesE8Explicit
public import CFSG.RankThree.PartOne.KE.CTMain

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.Sec66T
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionPhi_twenty_mod_five
  exact_E_type_and_triality_cross_prime_factor_exhaustion)


section Sectors


theorem layerSectorY_E8_excluded {e : ℕ}
    (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 8 ∨ e = 10 ∨ e = 12) :
    LayerSectorY Tag.E8 e :=
  LayerSectorY.of_two_le fun _ _ _ _ hp hp5 hpK hpe =>
    two_le_pRank_E8_of_sector hp hp5 hpK he hpe

theorem layerSectorY_E8_fifteen : LayerSectorY Tag.E8 15 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨-, -, hc⟩ := E8_fifteen_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (E8_fifteen_n0_odd _ hq2) hx hy2 hy1 hxy

theorem layerSectorY_E8_twenty : LayerSectorY Tag.E8 20 := by
  intro K _ _ p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr x hx hx1 hxσ y hy2 hy1 hxy
  exfalso
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases hp5' : 5 < p
  · have hK2 : Even (Nat.card K) := by
      rw [hKcard]
      exact Nat.even_pow.2 ⟨even_two, Nat.pos_iff_ne_zero.1 (Nat.mul_pos (by omega) hf₀)⟩
    obtain ⟨-, -, hc⟩ := E8_twenty_cyclic_sylow cyclic_torus_prime_centralizers K hp hp5' hpe
    have : Fact p.Prime := ⟨hp⟩
    exact not_commute_involution_of_cyclicSylow hc (E8_twenty_n0_odd _ hq2)
      (orderOf_eq_prime hx hx1) hy2 hy1 hxy
  · obtain rfl : p = 5 := by omega
    have h4 : (5 : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ) :=
      (exhaustionPhi_twenty_mod_five.2 _).1 (by exact_mod_cast hpe)
    have h2 := two_le_pRank_E8_of_sector hp hp5 (not_dvd_of_eq_two_pow hp hp5 hKcard) (e := 4)
      (by simp) (by exact_mod_cast h4)
    omega

theorem layerSectorY_E8_twentyfour : LayerSectorY Tag.E8 24 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨-, -, hc⟩ :=
      E8_twentyfour_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (E8_twentyfour_n0_odd _ hq2) hx hy2 hy1 hxy

theorem layerSectorY_E8_thirty : LayerSectorY Tag.E8 30 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨-, -, hc⟩ := E8_thirty_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (E8_thirty_n0_odd _ hq2) hx hy2 hy1 hxy

end Sectors

section Main

theorem lieGoodComponentFixT_E8_of_layers (h7 : LayerSector Tag.E8 7)
    (h9 : LayerSector Tag.E8 9) (h14 : LayerSector Tag.E8 14) (h18 : LayerSector Tag.E8 18) :
    LieGoodComponentFixT .E8 := by
  refine lieGood_of_sectors (τ := Tag.E8) rfl (stdForm_E78 rfl (Or.inr rfl))
    ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} : Finset ℕ) ?_ ?_
  · intro T _ _ p f hp hp5 hmod hpT
    exact ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega) (by omega)
      hmod).1 hpT).2.2.1 rfl
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact layerSectorY_E8_excluded (by simp)
    · exact layerSectorY_E8_excluded (by simp)
    · exact layerSectorY_E8_excluded (by simp)
    · exact layerSectorY_E8_excluded (by simp)
    · exact layerSectorY_E8_excluded (by simp)
    · exact layerSectorY_E8_excluded (by simp)
    · exact h7.toY
    · exact layerSectorY_E8_excluded (by simp)
    · exact h9.toY
    · exact layerSectorY_E8_excluded (by simp)
    · exact layerSectorY_E8_excluded (by simp)
    · exact h14.toY
    · exact layerSectorY_E8_fifteen
    · exact h18.toY
    · exact layerSectorY_E8_twenty
    · exact layerSectorY_E8_twentyfour
    · exact layerSectorY_E8_thirty

end Main

end CFSG.RankThree.PartOne.KLC
