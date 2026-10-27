module

public import CFSG.RankThree.PartOne.KLC.Descent
public import CFSG.RankThree.PartOne.KLC.EigE6
public import CFSG.RankThree.PartOne.KE.CTCasesE6Eight
public import CFSG.RankThree.PartOne.KE.CTCasesE6Nine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Twelve
public import CFSG.RankThree.PartOne.KE.CTMain

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.Sec66T
open CFSG.RankThree.Chevalley (exhaustionPhi
  exact_E_type_and_triality_cross_prime_factor_exhaustion)


section Odd

theorem odd_E6_eight {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd ((q ^ 4 + 1) * (q ^ 2 - 1)) := by
  refine Nat.odd_mul.2 ⟨?_, ?_⟩
  · have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    have h4 : 2 ∣ q ^ 4 := dvd_pow h1 (by norm_num)
    rw [Nat.odd_iff]
    omega
  · have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    have h2 : 2 ∣ q ^ 2 := dvd_pow h1 (by norm_num)
    have l : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.odd_iff]
    omega

end Odd

section Sectors


theorem layerSectorY_E6_excluded {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) :
    LayerSectorY Tag.E6 e :=
  LayerSectorY.of_two_le fun _ _ _ _ hp hp5 hpK hpe =>
    two_le_pRank_E6_of_sector hp hp5 hpK he hpe

theorem layerSectorY_E6_eight : LayerSectorY Tag.E6 8 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨-, -, hc⟩ := E6_eight_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (odd_E6_eight hK2 hq2) hx hy2 hy1 hxy

theorem layerSectorY_E6_nine : LayerSectorY Tag.E6 9 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    obtain ⟨-, -, hc⟩ := E6_nine_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (E6_nine_n0_odd _) hx hy2 hy1 hxy

theorem layerSectorY_E6_twelve : LayerSectorY Tag.E6 12 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    obtain ⟨-, -, hc⟩ := E6_twelve_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (E6_twelve_n0_odd _) hx hy2 hy1 hxy

end Sectors

section Main

theorem lieGoodComponentFixT_E6_of_layers (h5 : LayerSector Tag.E6 5) :
    LieGoodComponentFixT .E6 := by
  refine lieGood_of_sectors (τ := Tag.E6) rfl stdForm_E6
    ({1, 2, 3, 4, 5, 6, 8, 9, 12} : Finset ℕ) ?_ ?_
  · intro T _ _ p f hp hp5 hmod hpT
    exact ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega) (by omega)
      hmod).1 hpT).1 rfl
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact layerSectorY_E6_excluded (by simp)
    · exact layerSectorY_E6_excluded (by simp)
    · exact layerSectorY_E6_excluded (by simp)
    · exact layerSectorY_E6_excluded (by simp)
    · exact h5.toY
    · exact layerSectorY_E6_excluded (by simp)
    · exact layerSectorY_E6_eight
    · exact layerSectorY_E6_nine
    · exact layerSectorY_E6_twelve

end Main

end CFSG.RankThree.PartOne.KLC
