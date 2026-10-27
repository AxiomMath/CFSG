module

public import CFSG.Quasithin.Recognition.M12AscD2

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem not_inverts_of_odd {p x : G} (hp : Odd (orderOf p)) (hx : x * x * x = 1) (hx1 : x ≠ 1)
    (h : p * x * p⁻¹ = x⁻¹) : False := by
  have h1 : p * x⁻¹ * p⁻¹ = x := by
    have : p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ := by group
    rw [this, h, inv_inv]
  have key : ∀ n : ℕ, p ^ (2 * n + 1) * x * (p ^ (2 * n + 1))⁻¹ = x⁻¹ := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have e : p ^ (2 * (n + 1) + 1) = p * (p * p ^ (2 * n + 1)) := by
        rw [show 2 * (n + 1) + 1 = 1 + (1 + (2 * n + 1)) by ring, pow_add, pow_add, pow_one]
      rw [e]
      calc p * (p * p ^ (2 * n + 1)) * x * (p * (p * p ^ (2 * n + 1)))⁻¹
          = p * (p * (p ^ (2 * n + 1) * x * (p ^ (2 * n + 1))⁻¹) * p⁻¹) * p⁻¹ := by group
        _ = x⁻¹ := by rw [ih, h1, h]
  obtain ⟨k, hk⟩ := hp
  have := key k
  rw [← hk, pow_orderOf_eq_one] at this
  simp only [inv_one, one_mul, mul_one] at this
  apply hx1
  have hxx : x * x = 1 := by
    calc x * x = x * x⁻¹⁻¹ := by rw [inv_inv]
      _ = 1 := by rw [← this]; group
  calc x = x * x * x := by rw [hxx, one_mul]
    _ = 1 := hx

theorem mem_zpowers_of_cube_d4 {q t : G} (hq3 : q * q * q = 1) (h : t ∈ zpowers q) :
    t = 1 ∨ t = q ∨ t = q * q := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  have hq : q ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, pow_two]
    exact hq3
  have hk : q ^ k = q ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, hq, one_zpow, mul_one]
  rw [hk]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with e | e | e
  · left; rw [e]; simp
  · right; left; rw [e]; simp
  · right; right; rw [e]; exact zpow_two q

theorem sq_conj_eq_of_mem_zpowers {g q : G} (hq3 : q * q * q = 1) (hq1 : q ≠ 1)
    (h : g * q * g⁻¹ ∈ zpowers q) : g * g * q * (g * g)⁻¹ = q := by
  have hne : g * q * g⁻¹ ≠ 1 := by
    intro e
    apply hq1
    calc q = g⁻¹ * (g * q * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have hconj : g * g * q * (g * g)⁻¹ = g * (g * q * g⁻¹) * g⁻¹ := by group
  rw [hconj]
  rcases mem_zpowers_of_cube_d4 hq3 h with e | e | e
  · exact absurd e hne
  · rw [e]
    exact e
  · rw [e]
    calc g * (q * q) * g⁻¹ = (g * q * g⁻¹) * (g * q * g⁻¹) := by group
      _ = (q * q) * (q * q) := by rw [e]
      _ = q * q * q * q := by group
      _ = q := by rw [hq3, one_mul]

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem odd_orderOf_of_centralizes_D
    [Finite G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G)
    {g : G} (hg : ∀ d ∈ c.D, g * d = d * g) : Odd (orderOf g) := by
  classical
  obtain ⟨P, hPC, hPn, hzP, htr, hodd, hPodd, hxP, h9⟩ := m.exists_P hyp h27
  have hPoddord : ∀ p ∈ P, Odd (orderOf p) := fun p hp => by
    have h1 : orderOf (⟨p, hp⟩ : ↥P) ∣ Nat.card ↥P := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hPodd h1
  have hgx : g * m.ψ mX = m.ψ mX * g := hg _ c.x_mem_D
  have hgx1 : g * c.x1 = c.x1 * g := hg _ c.x1_mem_D
  have hgC : g ∈ Subgroup.centralizer ({m.ψ mX} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hgx
  have hz2 : z * z = 1 := c.z_sq
  rcases htr g hgC with hgP | hgzP
  · exact hPoddord g hgP
  · exfalso
    refine not_inverts_of_odd (hPoddord _ hgzP) c.x1_cube ?_ ?_
    · intro e
      have := c.x1_ord
      rw [e, orderOf_one] at this
      exact absurd this (by norm_num)
    · have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      calc g * z * c.x1 * (g * z)⁻¹ = g * (z * c.x1 * z⁻¹) * g⁻¹ := by group
        _ = g * c.x1⁻¹ * g⁻¹ := by rw [c.x1_z]
        _ = (g * c.x1 * g⁻¹)⁻¹ := by group
        _ = c.x1⁻¹ := by
          rw [show g * c.x1 * g⁻¹ = c.x1 by rw [hgx1]; group]

end AscCox

end CFSG.Quasithin
