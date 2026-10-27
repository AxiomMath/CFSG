module

public import CFSG.Quasithin.Recognition.M12AscD14
public import CFSG.Quasithin.Recognition.M12AscD13

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem not_normalizes_of_braid {L : Subgroup G} {v r : G} (hr : r ∈ L) (hr2 : r * r = 1)
    (hv2 : v * v = 1) (hrv : (r * v) ^ 3 = 1) (hvL : v ∉ L) : ∃ l ∈ L, v * l * v⁻¹ ∉ L := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  refine ⟨r, hr, fun hmem => hvL ?_⟩
  have e3 : (v * r) * (v * r) * (v * r) = 1 := by
    have h1 : (v * r) = (r * v)⁻¹ := by rw [mul_inv_rev, hri, hvi]
    calc (v * r) * (v * r) * (v * r) = (v * r) ^ 3 := by rw [pow_succ, pow_two]
      _ = ((r * v)⁻¹) ^ 3 := by rw [h1]
      _ = ((r * v) ^ 3)⁻¹ := by rw [inv_pow]
      _ = 1 := by rw [hrv, inv_one]
  have hbraid : v * r * v = r * v * r := by
    have : v * r * v * (r * v * r)⁻¹ = 1 := by
      calc v * r * v * (r * v * r)⁻¹ = v * r * v * (r⁻¹ * v⁻¹ * r⁻¹) := by group
        _ = v * r * v * (r * v * r) := by rw [hri, hvi]
        _ = (v * r) * (v * r) * (v * r) := by group
        _ = 1 := e3
    exact mul_inv_eq_one.1 this
  have h1 : r * v * r ∈ L := by
    rw [← hbraid]
    rw [hvi] at hmem
    exact hmem
  have : v = r * (r * v * r) * r := by
    calc v = (r * r) * v * (r * r) := by rw [hr2]; group
      _ = r * (r * v * r) * r := by group
  rw [this]
  exact mul_mem (mul_mem hr h1) hr

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem exists_vr
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G)
    {y : G} (h : OuterData c y) :
    ∃ v r : G, v * v = 1 ∧ (∀ k ∈ h.K, v * k * v⁻¹ ∈ h.K) ∧
      (∃ l ∈ h.L, v * l * v⁻¹ ∉ h.L) ∧ r ∈ h.L ∧ r ∉ h.K ∧ r * r = 1 ∧ (r * v) ^ 3 = 1 ∧
      (v * z) ^ 3 = 1 := by
  obtain ⟨v, hv⟩ := c.exists_v hyp h27 h
  have hvnorm := VData.normalizes_K c hyp h27 h hv
  have hvL := VData.not_mem_L c h hv
  have hv2 : v * v = 1 := hv.sq
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have ha2 : m.ψ mA * m.ψ mA = 1 := AscModel.a_sq
  have hai : (m.ψ mA)⁻¹ = m.ψ mA := inv_eq_of_mul_eq_one_right ha2
  have hb2 : (c.u' * z) * (c.u' * z) = 1 := c.b_sq
  have hbi : (c.u' * z)⁻¹ = c.u' * z := inv_eq_of_mul_eq_one_right hb2
  have hab : m.ψ mA * (c.u' * z) = (c.u' * z) * m.ψ mA := c.a_comm_b
  have hvb : v * (c.u' * z) = (c.u' * z) * v := hv.comm_b
  have hinv : (m.ψ mA * v) = (v * m.ψ mA)⁻¹ := by rw [mul_inv_rev, hai, hvi]
  have hav3 : (m.ψ mA * v) ^ 3 = ((v * m.ψ mA) ^ 3)⁻¹ := by rw [hinv, inv_pow]
  have hsignpa : Equiv.Perm.sign pa = 1 := by decide +kernel
  have hsignpba : Equiv.Perm.sign (pb * pa) = 1 := by decide +kernel
  have hnormpa : NormDb pa = false := by decide +kernel
  have hnormpba : NormDb (pb * pa) = false := by decide +kernel
  have hkey : ∀ r : G, r ∈ h.L → r ∉ h.K → r * r = 1 → (r * v) ^ 3 = 1 →
      ∃ v r : G, v * v = 1 ∧ (∀ k ∈ h.K, v * k * v⁻¹ ∈ h.K) ∧
        (∃ l ∈ h.L, v * l * v⁻¹ ∉ h.L) ∧ r ∈ h.L ∧ r ∉ h.K ∧ r * r = 1 ∧ (r * v) ^ 3 = 1 ∧
        (v * z) ^ 3 = 1 := by
    intro r hrL hrK hr2 hrv
    exact ⟨v, r, hv2, hvnorm, not_normalizes_of_braid hrL hr2 hv2 hrv hvL, hrL, hrK, hr2, hrv,
      hv.vz⟩
  have haL : m.ψ mA ∈ h.L := by
    rw [← c.ρ_pa]
    exact (h.rho_mem_L pa).2 hsignpa
  have haK : m.ψ mA ∉ h.K := by
    rw [← c.ρ_pa]
    intro hK
    have := ((h.rho_mem_K pa).1 hK).2
    rw [hnormpa] at this
    exact absurd this (by decide)
  have hbaL : (c.u' * z) * m.ψ mA ∈ h.L := by
    rw [← c.ρ_pb, ← c.ρ_pa, ← map_mul]
    exact (h.rho_mem_L _).2 hsignpba
  have hbaK : (c.u' * z) * m.ψ mA ∉ h.K := by
    rw [← c.ρ_pb, ← c.ρ_pa, ← map_mul]
    intro hK
    have := ((h.rho_mem_K _).1 hK).2
    rw [hnormpba] at this
    exact absurd this (by decide)
  rcases c.cube_va hyp hv with h1 | h1
  ·
    refine hkey (m.ψ mA) haL haK ha2 ?_
    rw [hav3, h1, inv_one]
  ·
    have hbva : Commute (c.u' * z) (m.ψ mA * v) := by
      show (c.u' * z) * (m.ψ mA * v) = (m.ψ mA * v) * (c.u' * z)
      calc (c.u' * z) * (m.ψ mA * v) = ((c.u' * z) * m.ψ mA) * v := by group
        _ = (m.ψ mA * (c.u' * z)) * v := by rw [hab]
        _ = m.ψ mA * ((c.u' * z) * v) := by group
        _ = m.ψ mA * (v * (c.u' * z)) := by rw [hvb]
        _ = (m.ψ mA * v) * (c.u' * z) := by group
    refine hkey ((c.u' * z) * m.ψ mA) hbaL hbaK ?_ ?_
    · calc (c.u' * z) * m.ψ mA * ((c.u' * z) * m.ψ mA)
          = (c.u' * z) * ((m.ψ mA * (c.u' * z)) * m.ψ mA) := by group
        _ = (c.u' * z) * (((c.u' * z) * m.ψ mA) * m.ψ mA) := by rw [hab]
        _ = ((c.u' * z) * (c.u' * z)) * (m.ψ mA * m.ψ mA) := by group
        _ = 1 := by rw [hb2, ha2, mul_one]
    · calc ((c.u' * z) * m.ψ mA * v) ^ 3 = ((c.u' * z) * (m.ψ mA * v)) ^ 3 := by rw [mul_assoc]
        _ = (c.u' * z) ^ 3 * (m.ψ mA * v) ^ 3 := hbva.mul_pow 3
        _ = 1 := by
          have hb3 : (c.u' * z) ^ 3 = c.u' * z := by rw [pow_succ, pow_two, hb2, one_mul]
          rw [hav3, h1, hbi, hb3, hb2]

end AscCox

end CFSG.Quasithin
