module

public import CFSG.Quasithin.Recognition.M12AscD5

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem exists_split {A : Type*} [Group A] (τ : A →* A) (hτ : ∀ a, τ (τ a) = a)
    (hcomm : ∀ a b : A, a * b = b * a) {q : A} (hq : Odd (orderOf q)) :
    ∃ cp cm : A, q = cp * cm ∧ τ cp = cp ∧ τ cm = cm⁻¹ := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  obtain ⟨k, hk⟩ := hq
  have hqk : q ^ (2 * (k + 1)) = q := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk, pow_orderOf_eq_one, one_mul]
  refine ⟨(q * τ q) ^ (k + 1), (q * (τ q)⁻¹) ^ (k + 1), ?_, ?_, ?_⟩
  · rw [← mul_pow]
    calc q = q ^ (2 * (k + 1)) := hqk.symm
      _ = (q * q) ^ (k + 1) := by rw [pow_mul, sq]
      _ = (q * τ q * (q * (τ q)⁻¹)) ^ (k + 1) := by
        congr 1
        rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
  · rw [map_pow, map_mul, hτ, mul_comm]
  · rw [map_pow, map_mul, map_inv, hτ, ← inv_pow, mul_inv_rev, inv_inv, mul_comm]

theorem eq_zpowers_of_odd_sub [Finite G] {H S : Subgroup G} (hH : Nat.card H = 192) (hS : S ≤ H)
    (hodd : ∀ g ∈ S, Odd (orderOf g)) {q : G} (hqS : q ∈ S) (hq1 : q ≠ 1) :
    S = zpowers q ∧ orderOf q = 3 := by
  have hS3 : Nat.card S ∣ 3 := card_dvd_three_of_odd hH hS hodd
  have hqo3 : orderOf q ∣ 3 := by
    have h1 : orderOf (⟨q, hqS⟩ : ↥S) ∣ Nat.card ↥S := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans hS3
  have hq1' : orderOf q ≠ 1 := fun e => hq1 (orderOf_eq_one_iff.1 e)
  have hqo : orderOf q = 3 := ((Nat.dvd_prime Nat.prime_three).1 hqo3).resolve_left hq1'
  have hcardz : Nat.card (zpowers q) = 3 := by rw [Nat.card_zpowers, hqo]
  have hzS : zpowers q ≤ S := (Subgroup.zpowers_le).2 hqS
  have h1 : Nat.card (zpowers q) ∣ Nat.card S := Subgroup.card_dvd_of_le hzS
  have h2 : Nat.card S = 3 := Nat.dvd_antisymm hS3 (hcardz ▸ h1)
  exact ⟨(Subgroup.eq_of_le_of_card_ge hzS (by rw [h2, hcardz])).symm, hqo⟩

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem x1_ne : c.x1 ≠ 1 := fun e => by
  have := c.x1_ord
  rw [e, orderOf_one] at this
  omega

theorem C_comm
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G) {y : G}
    (h : OuterData c y) {p p' : G} (hp : p ∈ Subgroup.centralizer (c.D : Set G))
    (hp' : p' ∈ Subgroup.centralizer (c.D : Set G)) : p * p' = p' * p := by
  have h1 := c.b_inverts_C hyp h27 h hp
  have h2 := c.b_inverts_C hyp h27 h hp'
  have h3 := c.b_inverts_C hyp h27 h (mul_mem hp hp')
  have h4 : p⁻¹ * p'⁻¹ = p'⁻¹ * p⁻¹ := by
    calc p⁻¹ * p'⁻¹ = ((c.u' * z) * p * (c.u' * z)⁻¹) * ((c.u' * z) * p' * (c.u' * z)⁻¹) := by
          rw [h1, h2]
      _ = (c.u' * z) * (p * p') * (c.u' * z)⁻¹ := by group
      _ = (p * p')⁻¹ := h3
      _ = p'⁻¹ * p⁻¹ := by group
  calc p * p' = (p'⁻¹ * p⁻¹)⁻¹ := by group
    _ = (p⁻¹ * p'⁻¹)⁻¹ := by rw [h4]
    _ = p' * p := by group

theorem mem_D_of_fixed_z
    [Finite G] {q : G} (hq : ∀ d ∈ c.D, q * d = d * q) (hz : z * q * z⁻¹ = q) : q ∈ c.D := by
  have hz2 : z * z = 1 := c.z_sq
  have hzx : m.ψ mX * z = z * m.ψ mX := m.ψ_comm_z mX
  have hqz : q * z = z * q := by
    calc q * z = (z * q * z⁻¹) * z := by rw [hz]
      _ = z * q := by group
  have hqH : q ∈ ascH z := Subgroup.mem_centralizer_singleton_iff.2 hqz
  have hqx : q * m.ψ mX = m.ψ mX * q := hq _ c.x_mem_D
  obtain ⟨k, hk6, hk⟩ := m.CHx hqH hqx
  have hxH : m.ψ mX ∈ ascH z := m.ψ_mem mX
  have hxzH : m.ψ mX * z ∈ ascH z := mul_mem hxH (z_mem_ascH z)
  have hqe : q = (m.ψ mX * z) ^ k := by
    apply m.tb_inj hqH (pow_mem hxzH k)
    rw [hk, m.tb_pow hxzH k, m.tb_mul hxH (z_mem_ascH z), m.tb_ψ_mX, m.tb_z]
  have hxzc : Commute (m.ψ mX) z := hzx
  have hsq : (m.ψ mX * z) ^ 2 = m.ψ mX * m.ψ mX := by
    calc (m.ψ mX * z) ^ 2 = m.ψ mX * (z * m.ψ mX) * z := by rw [pow_two]; group
      _ = m.ψ mX * (m.ψ mX * z) * z := by rw [← hzx]
      _ = m.ψ mX * m.ψ mX * (z * z) := by group
      _ = m.ψ mX * m.ψ mX := by rw [hz2, mul_one]
  have hxx : m.ψ mX * m.ψ mX ∈ c.D := mul_mem c.x_mem_D c.x_mem_D
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [hqe, pow_mul, hsq]
    exact pow_mem hxx j
  · exfalso
    have hd : (m.ψ mX * m.ψ mX) ^ j * m.ψ mX ∈ c.D := mul_mem (pow_mem hxx j) c.x_mem_D
    have hqe' : q = ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * z := by
      rw [hqe, pow_succ, pow_mul, hsq, ← mul_assoc]
    have hx1 : q * c.x1 = c.x1 * q := hq _ c.x1_mem_D
    have hdx1 : ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * c.x1 = c.x1 * ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) :=
      c.D_comm hd c.x1_mem_D
    have key : c.x1 = c.x1⁻¹ := by
      calc c.x1 = q * c.x1 * q⁻¹ := by rw [hx1]; group
        _ = (((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * z) * c.x1 * (((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * z)⁻¹ := by
          rw [← hqe']
        _ = ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * (z * c.x1 * z⁻¹) * ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX)⁻¹ := by
          group
        _ = ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * c.x1⁻¹ * ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX)⁻¹ := by
          rw [c.x1_z]
        _ = c.x1⁻¹ := by
          have : ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * c.x1⁻¹ = c.x1⁻¹ * ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) := by
            have := hdx1
            calc ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * c.x1⁻¹
                = c.x1⁻¹ * (c.x1 * ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX)) * c.x1⁻¹ := by group
              _ = c.x1⁻¹ * (((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) * c.x1) * c.x1⁻¹ := by rw [hdx1]
              _ = c.x1⁻¹ * ((m.ψ mX * m.ψ mX) ^ j * m.ψ mX) := by group
          rw [this]
          group
    apply c.x1_ne
    have hxx1 : c.x1 * c.x1 = 1 := by
      calc c.x1 * c.x1 = c.x1 * c.x1⁻¹ := by rw [← key]
        _ = 1 := by group
    calc c.x1 = c.x1 * c.x1 * c.x1 := by rw [hxx1, one_mul]
      _ = 1 := c.x1_cube

end AscCox

end CFSG.Quasithin
