module

public import CFSG.Quasithin.EmptyFaithful.SzN2Sp
public import CFSG.Quasithin.EmptyFaithful.S153F17
public import CFSG.Quasithin.EmptyFaithful.S153F20

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

private theorem exists_card_four_of_card_two_pow {F : Type} [Fintype F] {n : ℕ}
    (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n) : ∃ s : Finset F, s.card = 4 := by
  have h4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
    (by simpa using h4)
  exact ⟨s, hs⟩

theorem solvOvergroupsThreePrime_holds : SolvOvergroupsThreePrime := by
  intro G _ _ L S₀ X hq hS hSX hXL hXs
  obtain ⟨n, F, hF, hFin, hodd, hn3, hcard, hq⟩ := hq
  have hnat : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hnat⟩
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
  have hK4 := exists_card_four_of_card_two_pow (by omega) hcard
  have h3 : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hnat]
    exact SzN2.not_three_dvd_two_pow_sub_one hodd
  rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨ρ, hρ, hk⟩ := SzN2.exists_hom_of_quotient_equiv e
    exact SzN2.L_not_three_dvd_of_solvable_overgroup ρ hρ hk
      (SzN2.sl_no_order_three (n := 2) (by norm_num) hK h3
        (fun A hA hs => SzN2.sl2_le_upperTriangular_of_solvable hK4 hA hs)) hS hSX hXL hXs
  · obtain ⟨ρ, hρ, hk⟩ := SzN2.exists_hom_of_quotient_equiv
      (e.trans (specialLinearGroupEquivStatedSL 3 F).symm)
    exact SzN2.L_not_three_dvd_of_solvable_overgroup ρ hρ hk
      (SzN2.sl_no_order_three (n := 3) (by norm_num) hK h3
        (fun A hA hs => SzN2.sl3_le_upperTriangular_of_solvable hK4 hA hs)) hS hSX hXL hXs

theorem solvOvergroupsInBorel_holds : SolvOvergroupsInBorel := by
  intro G _ _ L S₀ X hq hS hSX hXL hXs
  rcases hq with ⟨n, F, hF, hFin, hn1, hcard, ⟨e⟩⟩ | ⟨F, hF, hFin, hcard, ⟨e⟩⟩
  · have hnat : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
    have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hnat⟩
    have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
    have hK4 := exists_card_four_of_card_two_pow (by omega) hcard
    obtain ⟨ρ, hρ, hk⟩ := SzN2.exists_hom_of_quotient_equiv
      (e.trans (specialLinearGroupEquivStatedSL 3 F).symm)
    exact SzN2.L_normalizes_of_solvable_overgroup ρ hρ hk
      (SzN2.sl_solvable_overgroup_le_normalizer (n := 3) (by norm_num)
        (fun A hA hs => SzN2.sl3_le_upperTriangular_of_solvable hK4 hA hs)) hS hSX hXL hXs
  · have hnat : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]; norm_num
    have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨2, hnat⟩
    have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
    have hK4 := exists_card_four_of_card_two_pow (n := 2) (by omega) (by rw [hcard]; norm_num)
    obtain ⟨ρ, hρ, hk⟩ := SzN2.exists_hom_of_quotient_equiv e
    exact SzN2.L_normalizes_of_solvable_overgroup ρ hρ hk
      (SzN2.sp4_solvable_overgroup_le_normalizer hK4) hS hSX hXL hXs

theorem rankTwoMaxParabolics_holds : RankTwoMaxParabolics := by
  intro G _ _ L S₀ hq hS
  rcases hq with ⟨n, F, hF, hFin, hn1, hcard, ⟨e⟩⟩ | ⟨F, hF, hFin, hcard, ⟨e⟩⟩
  · have hnat : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
    have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hnat⟩
    have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
    obtain ⟨ρ, hρ, hk⟩ := SzN2.exists_hom_of_quotient_equiv
      (e.trans (specialLinearGroupEquivStatedSL 3 F).symm)
    exact SzN2.L_exists_maxParabolic_pair ρ hρ hk (SzN2.sl3_rankTwoData hK) hS
  · have hnat : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]; norm_num
    have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨2, hnat⟩
    have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hnat
    obtain ⟨ρ, hρ, hk⟩ := SzN2.exists_hom_of_quotient_equiv e
    exact SzN2.L_exists_maxParabolic_pair ρ hρ hk (SzN2.sp4_rankTwoData hK) hS

end CFSG.Quasithin
