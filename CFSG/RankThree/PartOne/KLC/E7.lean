module

public import CFSG.RankThree.PartOne.KLC.Descent
public import CFSG.RankThree.PartOne.KLC.EigE7
public import CFSG.RankThree.PartOne.KLC.Degenerate
public import CFSG.RankThree.PartOne.KE.CTCasesE7Sev
public import CFSG.RankThree.PartOne.KE.CTCasesE7CoxNine
public import CFSG.RankThree.PartOne.KE.CTCasesE7CoxEighteen
public import CFSG.RankThree.PartOne.KE.CTMain

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley (exhaustionPhi
  exact_E_type_and_triality_cross_prime_factor_exhaustion)


section Odd

theorem odd_E7_seven {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd ((q ^ 6 + q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q - 1)) := by
  refine Nat.odd_mul.2 ⟨?_, ?_⟩
  · have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    have h2 : 2 ∣ q ^ 2 := dvd_pow h1 (by norm_num)
    have h3 : 2 ∣ q ^ 3 := dvd_pow h1 (by norm_num)
    have h4 : 2 ∣ q ^ 4 := dvd_pow h1 (by norm_num)
    have h5 : 2 ∣ q ^ 5 := dvd_pow h1 (by norm_num)
    have h6 : 2 ∣ q ^ 6 := dvd_pow h1 (by norm_num)
    rw [Nat.odd_iff]
    omega
  · rw [Nat.odd_iff]
    have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    omega

theorem odd_E7_nine {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd ((q ^ 6 + q ^ 3 + 1) * (q - 1)) := by
  refine Nat.odd_mul.2 ⟨?_, ?_⟩
  · have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    have h3 : 2 ∣ q ^ 3 := dvd_pow h1 (by norm_num)
    have h6 : 2 ∣ q ^ 6 := dvd_pow h1 (by norm_num)
    rw [Nat.odd_iff]
    omega
  · rw [Nat.odd_iff]
    have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
    omega

theorem odd_E7_fourteen {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd ((q ^ 6 - q ^ 5 + q ^ 4 - q ^ 3 + q ^ 2 - q + 1) * (q + 1)) := by
  refine Nat.odd_mul.2 ⟨?_, hq.add_one⟩
  have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
  have h2 : 2 ∣ q ^ 2 := dvd_pow h1 (by norm_num)
  have h3 : 2 ∣ q ^ 3 := dvd_pow h1 (by norm_num)
  have h4 : 2 ∣ q ^ 4 := dvd_pow h1 (by norm_num)
  have h5 : 2 ∣ q ^ 5 := dvd_pow h1 (by norm_num)
  have h6 : 2 ∣ q ^ 6 := dvd_pow h1 (by norm_num)
  have l65 : q ^ 5 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have l43 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have l21 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  rw [Nat.odd_iff]
  omega

theorem odd_E7_eighteen {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    Odd ((q ^ 6 - q ^ 3 + 1) * (q + 1)) := by
  refine Nat.odd_mul.2 ⟨?_, hq.add_one⟩
  have h1 : 2 ∣ q := even_iff_two_dvd.1 hq
  have h3 : 2 ∣ q ^ 3 := dvd_pow h1 (by norm_num)
  have h6 : 2 ∣ q ^ 6 := dvd_pow h1 (by norm_num)
  have l : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [Nat.odd_iff]
  omega

end Odd

section Sectors


theorem layerSectorY_E7_excluded {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6) :
    LayerSectorY Tag.E7 e :=
  LayerSectorY.of_two_le fun _ _ _ _ hp hp5 hpK hpe =>
    two_le_pRank_E7_of_sector hp hp5 hpK he hpe

theorem layerSectorY_E7_seven : LayerSectorY Tag.E7 7 := by
  intro K _ _ p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr x hx hx1 hxσ y hy2 hy1 hxy
  exfalso
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK2 : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.2 ⟨even_two, Nat.pos_iff_ne_zero.1 (Nat.mul_pos (by omega) hf₀)⟩
  by_cases hp7 : 7 < p
  · obtain ⟨-, hc⟩ := E7_seven_cyclic_sylow cyclic_torus_prime_centralizers K hp hp7 hpe
    have : Fact p.Prime := ⟨hp⟩
    exact not_commute_involution_of_cyclicSylow hc (odd_E7_seven hK2 hq2)
      (orderOf_eq_prime hx hx1) hy2 hy1 hxy
  · have h1 := dvd_sub_one_of_dvd_phi_seven_of_le hp hp5 (by omega) hpe
    have h2 := two_le_pRank_E7_of_sector hp hp5 (not_dvd_of_eq_two_pow hp hp5 hKcard) (e := 1)
      (by simp) (by simpa [exhaustionPhi] using h1)
    omega

theorem layerSectorY_E7_nine : LayerSectorY Tag.E7 9 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨-, -, hc⟩ := E7_nine_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (odd_E7_nine hK2 hq2) hx hy2 hy1 hxy

theorem layerSectorY_E7_fourteen : LayerSectorY Tag.E7 14 := by
  intro K _ _ p f₀ hp hp5 hf₀ hKcard σ hσ hpe hpr x hx hx1 hxσ y hy2 hy1 hxy
  exfalso
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK2 : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.2 ⟨even_two, Nat.pos_iff_ne_zero.1 (Nat.mul_pos (by omega) hf₀)⟩
  by_cases hp7 : 7 < p
  · obtain ⟨-, hc⟩ := E7_fourteen_cyclic_sylow cyclic_torus_prime_centralizers K hp hp7 hpe
    have : Fact p.Prime := ⟨hp⟩
    exact not_commute_involution_of_cyclicSylow hc (odd_E7_fourteen hK2 hq2)
      (orderOf_eq_prime hx hx1) hy2 hy1 hxy
  · have h1 := dvd_add_one_of_dvd_phi_fourteen_of_le hp hp5 (by omega) hpe
    have h2 := two_le_pRank_E7_of_sector hp hp5 (not_dvd_of_eq_two_pow hp hp5 hKcard) (e := 2)
      (by simp) (by simpa [exhaustionPhi] using h1)
    omega

theorem layerSectorY_E7_eighteen : LayerSectorY Tag.E7 18 :=
  LayerSectorY.of_no_commuting fun K _ _ p hp hp5 hK2 hpe x y hx hy2 hy1 hxy => by
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    obtain ⟨-, -, hc⟩ :=
      E7_eighteen_cyclic_sylow cyclic_torus_prime_centralizers K hp (by omega) hpe
    exact not_commute_involution_of_cyclicSylow hc (odd_E7_eighteen hK2 hq2) hx hy2 hy1 hxy

end Sectors

section Main

theorem lieGoodComponentFixT_E7_of_layers (h5 : LayerSector Tag.E7 5)
    (h8 : LayerSector Tag.E7 8) (h10 : LayerSector Tag.E7 10) (h12 : LayerSector Tag.E7 12) :
    LieGoodComponentFixT .E7 := by
  refine lieGood_of_sectors (τ := Tag.E7) rfl (stdForm_E78 rfl (Or.inl rfl))
    ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18} : Finset ℕ) ?_ ?_
  · intro T _ _ p f hp hp5 hmod hpT
    exact ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega) (by omega)
      hmod).1 hpT).2.1 rfl
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact layerSectorY_E7_excluded (by simp)
    · exact layerSectorY_E7_excluded (by simp)
    · exact layerSectorY_E7_excluded (by simp)
    · exact layerSectorY_E7_excluded (by simp)
    · exact h5.toY
    · exact layerSectorY_E7_excluded (by simp)
    · exact layerSectorY_E7_seven
    · exact h8.toY
    · exact layerSectorY_E7_nine
    · exact h10.toY
    · exact h12.toY
    · exact layerSectorY_E7_fourteen
    · exact layerSectorY_E7_eighteen

end Main

end CFSG.RankThree.PartOne.KLC
