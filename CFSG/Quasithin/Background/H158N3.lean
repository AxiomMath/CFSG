module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.H158N

open CFSG.Quasithin

theorem not_le_of_rk {V : Type*} [CommGroup V] {A B : Subgroup V} (hA : rk ↥A = 7)
    (hB : rk ↥B = 3) : ¬ A ≤ B := by
  intro hAB
  unfold rk at hA hB
  have hA0 : Nat.card ↥A ≠ 0 := by
    intro h0
    rw [h0, padicValNat.zero] at hA
    exact absurd hA (by norm_num)
  have hB0 : Nat.card ↥B ≠ 0 := by
    intro h0
    rw [h0, padicValNat.zero] at hB
    exact absurd hB (by norm_num)
  have h7 : 2 ^ 7 ∣ Nat.card ↥A := by
    have h := pow_padicValNat_dvd (p := 2) (n := Nat.card ↥A)
    rw [hA] at h
    exact h
  have h7B : 2 ^ 7 ∣ Nat.card ↥B := h7.trans (Subgroup.card_dvd_of_le hAB)
  have h7le := (padicValNat_dvd_iff_le hB0).1 h7B
  omega

theorem eq_of_fixV_normalized {V : Type*} [CommGroup V] {K P : Subgroup (MulAut V)} {z : V}
    (hPK : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hz1 : z ≠ 1) (hzK : ∀ k ∈ K, k z = z)
    (hfix : ∀ w : V, (∀ k ∈ K, k w = w) → w = 1 ∨ w = z) : ∀ g ∈ P, g z = z := by
  intro g hg
  have hkz : ∀ k ∈ K, k (g z) = g z := by
    intro k hk
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K := hPK g⁻¹ (P.inv_mem hg) k hk
    have h1 := hzK _ hk'
    calc k (g z) = g ((g⁻¹ * k * g⁻¹⁻¹) z) := by
          simp [MulAut.mul_apply]
      _ = g z := by rw [h1]
  rcases hfix (g z) hkz with h | h
  · exact absurd (g.injective (h.trans (map_one g).symm)) hz1
  · exact h

end CFSG.Quasithin.H158N
