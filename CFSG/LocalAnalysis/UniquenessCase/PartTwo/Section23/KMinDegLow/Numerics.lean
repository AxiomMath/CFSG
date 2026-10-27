module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.LeviData
import CFSG.Blueprint.LieModelAPI
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow

open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

private theorem three_not_dvd_ordSuzuki_two_pow {f : ℕ} (hf : Odd f) :
    ¬ 3 ∣ CFSG.Open.ordSuzuki (2 ^ f) := by
  obtain ⟨k, rfl⟩ := hf
  set q := 2 ^ (2 * k + 1) with hqdef
  have hq : q % 3 = 2 := by
    rw [hqdef, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hq21 : (q ^ 2 + 1) % 3 = 2 := by
    rw [Nat.add_mod, hq2]
  have hq1 : (q - 1) % 3 = 1 := by
    rw [← Nat.mod_sub_of_le (n := 3) (a := q) (b := 1) (by omega)]
    omega
  have hprod : q ^ 2 * (q ^ 2 + 1) * (q - 1) % 3 = 2 := by
    simp only [Nat.mul_mod, Nat.mod_mod, hq2, hq21, hq1]
  intro h
  unfold CFSG.Open.ordSuzuki at h
  have h0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [hprod] at h0
  norm_num at h0

theorem le_of_dvd_card_l2 {T A : Type} [Group T] [Group A] [Finite A] {n n₀ : ℕ}
    (hT : LeviData T n) (hn : 2 < n) (hA : IsL2 A n₀) (hn₀ : 2 < n₀)
    (h : Nat.card T ∣ Nat.card A) : n ≤ n₀ := by
  have hAord : Nat.card A = CFSG.Open.ordA 1 (2 ^ n₀) := by
    have hSC : CFSG.Open.StatedClassicalModel A .PSL 2 2 n₀ :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA
    exact (card_statedClassicalModel_two hSC).1 rfl
  obtain ⟨m, hm2, -, -, hp⟩ := hT.bound
  by_cases hmn : m * n = 6
  · have hnle : n ≤ 3 := by
      have h2n : 2 * n ≤ 6 := by
        calc 2 * n ≤ m * n := Nat.mul_le_mul_right n hm2
          _ = 6 := hmn
      exact Nat.le_of_mul_le_mul_left (by simpa using h2n) (by norm_num)
    omega
  · obtain ⟨p, hpp, hpdvd⟩ := hp hmn
    have hpdvd' : p ∣ CFSG.Open.ordA 1 (2 ^ n₀) := by
      rw [← hAord]
      exact hpdvd.trans h
    have hk : 0 < m * n := Nat.mul_pos (by omega) (by omega)
    have hz : zA 1 n₀ (m * n) :=
      ((profile_ordA (n := 1) (f := n₀) le_rfl (by omega)).prim p (m * n) hpp hk).mp hpdvd'
    have hle : m * n ≤ n₀ * 2 := zA_le (by omega) hz
    have h2n : 2 * n ≤ m * n := Nat.mul_le_mul_right n hm2
    have h2n' : 2 * n ≤ 2 * n₀ := by
      rw [← Nat.mul_comm n₀ 2]
      exact h2n.trans hle
    exact Nat.le_of_mul_le_mul_left h2n' (by norm_num)

theorem le_of_dvd_card_sz
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    {T A : Type} [Group T] [Group A] [Finite A] {n n₀ : ℕ}
    (hT : LeviData T n) (hn : 2 < n) (hA : IsSz A n₀) (hn₀ : 2 < n₀)
    (h : Nat.card T ∣ Nat.card A) : n ≤ n₀ := by
  have hAord : Nat.card A = CFSG.Open.ordSuzuki (2 ^ n₀) := hSz A n₀ hA
  obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := (CFSG.Blueprint.LieModel.suzukiModel hA).2
  have hodd : Odd n₀ := ⟨a, by omega⟩
  obtain ⟨m, hm2, h3, -, hp⟩ := hT.bound
  have hm4 : m = 4 := by
    rcases h3 with h3 | h3
    · exfalso
      have h3A : 3 ∣ Nat.card A := h3.trans h
      rw [hAord] at h3A
      exact three_not_dvd_ordSuzuki_two_pow hodd h3A
    · exact h3
  have hmn : m * n ≠ 6 := by
    rintro h
    rw [hm4] at h
    omega
  obtain ⟨p, hpp, hpdvd⟩ := hp hmn
  have hpdvd' : p ∣ CFSG.Open.ordSuzuki (2 ^ n₀) := by
    rw [← hAord]
    exact hpdvd.trans h
  have hk : 0 < m * n := Nat.mul_pos (by omega) (by omega)
  have hz : zSz n₀ (m * n) :=
    ((profile_ordSuzuki (f := n₀) (by omega)).prim p (m * n) hpp hk).mp hpdvd'
  have hle : m * n ≤ 2 * (n₀ * 2) := zSz_le (by omega) hz
  have h4n : 4 * n ≤ 4 * n₀ := by
    calc 4 * n = m * n := by rw [hm4]
      _ ≤ 2 * (n₀ * 2) := hle
      _ = 4 * n₀ := by ring
  exact Nat.le_of_mul_le_mul_left h4n (by norm_num)

theorem le_nine_of_dvd_card_u3_three {T A : Type} [Group T] [Group A] [Finite A] {n : ℕ}
    (hT : LeviData T n) (hn : 2 < n) (hA : IsU3 A 3) (h : Nat.card T ∣ Nat.card A) : n ≤ 9 := by
  have hAord : Nat.card A = CFSG.Open.ordTwistedA 2 (2 ^ 3) := by
    have hSC : CFSG.Open.StatedClassicalModel A .PSU 3 2 3 :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA
    exact (card_statedClassicalModel_two hSC).2.1 rfl
  obtain ⟨m, hm2, -, -, hp⟩ := hT.bound
  have hle : m * n ≤ 18 := by
    by_cases hmn : m * n = 6
    · omega
    · obtain ⟨p, hpp, hpdvd⟩ := hp hmn
      have hpdvd' : p ∣ CFSG.Open.ordTwistedA 2 (2 ^ 3) := by
        rw [← hAord]
        exact hpdvd.trans h
      have hk : 0 < m * n := Nat.mul_pos (by omega) (by omega)
      have hz : zU 2 3 (m * n) :=
        ((profile_ordTwistedA (n := 2) (g := 3) le_rfl (by norm_num)).prim p (m * n) hpp
          hk).mp hpdvd'
      have h := zU_le (n := 2) (g := 3) (t := 1) (Or.inl (by norm_num)) (by norm_num) hz
      simpa using h
  have h2n : 2 * n ≤ m * n := Nat.mul_le_mul_right n hm2
  exact Nat.le_of_mul_le_mul_left (h2n.trans hle) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow
