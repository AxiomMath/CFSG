module

public import CFSG.Quasithin.Recognition.M12AscD12

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem z_mem_Qs [Finite G] (c : AscCox m) (hyp : Asc03Hyp G z) : z ∈ ascQ (z * m.ψ mA) := by
  have haQ : m.ψ mA ∈ ascQ z := m.fSub_le_ascQ hyp AscModel.a_mem_F
  have hzQ : z ∈ ascQ z := AscModel.z_mem_ascQ hyp
  have hs : IsConj z (z * m.ψ mA) := isConj_iff.2 ⟨c.g, c.g_conj⟩
  have hsQ : z * m.ψ mA ∈ ascQ z := mul_mem hzQ haQ
  have hne : z ≠ z * m.ψ mA := by
    intro e
    apply AscModel.a_ne_one (m := m)
    calc m.ψ mA = z⁻¹ * (z * m.ψ mA) := by group
      _ = z⁻¹ * z := by rw [← e]
      _ = 1 := by group
  exact mem_ascQ_symm hyp (IsConj.refl z) hs hne hsQ

theorem s_mem_Qb [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) :
    z * m.ψ mA ∈ ascQ (c.u' * z) := by
  have hbconj := c.isConj_b hyp
  have hsconj : IsConj z (z * m.ψ mA) := isConj_iff.2 ⟨c.g, c.g_conj⟩
  have hbQs : c.u' * z ∈ ascQ (z * m.ψ mA) := mul_mem c.u'_Qs (c.z_mem_Qs hyp)
  have haQ : m.ψ mA ∈ ascQ z := m.fSub_le_ascQ hyp AscModel.a_mem_F
  have hne : z * m.ψ mA ≠ c.u' * z := by
    intro e
    apply c.u_notin_Qz hyp
    have hzu : z * c.u' = c.u' * z := c.u_facts.2.2
    have : m.ψ mA = c.u' := by
      calc m.ψ mA = z⁻¹ * (z * m.ψ mA) := by group
        _ = z⁻¹ * (c.u' * z) := by rw [e]
        _ = z⁻¹ * (z * c.u') := by rw [hzu]
        _ = c.u' := by group
    rw [← this]
    exact haQ
  exact mem_ascQ_symm hyp hsconj hbconj hne hbQs

theorem a_comm_b : m.ψ mA * (c.u' * z) = (c.u' * z) * m.ψ mA := by
  obtain ⟨h1, h2, h3⟩ := c.u_facts
  have haz : m.ψ mA * z = z * m.ψ mA := m.ψ_comm_z mA
  calc m.ψ mA * (c.u' * z) = (m.ψ mA * c.u') * z := by group
    _ = (c.u' * m.ψ mA) * z := by rw [h2]
    _ = c.u' * (m.ψ mA * z) := by group
    _ = c.u' * (z * m.ψ mA) := by rw [haz]
    _ = (c.u' * z) * m.ψ mA := by group

theorem VData.ne_z {v : G} (hv : VData c v) : v ≠ z := by
  intro e
  have h1 := hv.act_x1
  rw [e] at h1
  have h2 : c.ρ (swap 0 1) * c.ρ x16 * (c.ρ (swap 0 1))⁻¹ =
      c.ρ (swap 0 1 * x16 * (swap 0 1)⁻¹) := by rw [map_mul, map_mul, map_inv]
  rw [c.ρ_z] at h2
  have h3 : c.ρ bv = c.ρ (swap 0 1 * x16 * (swap 0 1)⁻¹) := h1.symm.trans h2
  exact absurd (c.ρ_inj h3) (by decide +kernel)

theorem cube_va
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {v : G} (hv : VData c v) :
    (v * m.ψ mA) ^ 3 = 1 ∨ (v * m.ψ mA) ^ 3 = c.u' * z := by
  have hbconj := c.isConj_b hyp
  obtain ⟨mb⟩ := exists_model_of_isConj m hbconj
  have hypb := asc03Hyp_of_isConj hyp hbconj
  have hs := c.s_mem_Qb hyp
  have hz2 : z * z = 1 := c.z_sq
  have hvH : v ∈ ascH (c.u' * z) := Subgroup.mem_centralizer_singleton_iff.2 hv.comm_b
  have haH : m.ψ mA ∈ ascH (c.u' * z) := Subgroup.mem_centralizer_singleton_iff.2 c.a_comm_b
  have hzH : z ∈ ascH (c.u' * z) := Subgroup.mem_centralizer_singleton_iff.2 c.b_comm_z
  have hg0H : v * z ∈ ascH (c.u' * z) := mul_mem hvH hzH
  have hhH : v * m.ψ mA ∈ ascH (c.u' * z) := mul_mem hvH haH
  set g0 := v * z with hg0
  set s := z * m.ψ mA with hsdef
  have hg03 : g0 ^ 3 = 1 := hv.vz
  have hh : v * m.ψ mA = g0 * s := by
    rw [hg0, hsdef]
    calc v * m.ψ mA = v * (z * z) * m.ψ mA := by rw [hz2, mul_one]
      _ = v * z * (z * m.ψ mA) := by group
  have hg01 : g0 ≠ 1 := by
    intro e
    apply hv.ne_z
    calc v = v * z * z⁻¹ := by group
      _ = z⁻¹ := by rw [← hg0, e, one_mul]
      _ = z := inv_eq_of_mul_eq_one_right hz2
  have hqSub : ascQ (c.u' * z) = mb.qSub := mb.ascQ_eq_qSub hypb
  have hsq : s ∈ mb.qSub := by rw [← hqSub]; exact hs
  have hnorm : ∀ q ∈ mb.qSub, ∀ t ∈ ascH (c.u' * z), t * q * t⁻¹ ∈ mb.qSub :=
    fun q hq t ht => mb.qSub_normal ht hq
  have hg0i : g0⁻¹ ∈ ascH (c.u' * z) := inv_mem hg0H
  have hc1 : g0⁻¹ * s * g0 ∈ mb.qSub := by
    have := hnorm s hsq g0⁻¹ hg0i
    simpa using this
  have hc2 : g0⁻¹ * (g0⁻¹ * s * g0) * g0 ∈ mb.qSub := by
    have := hnorm _ hc1 g0⁻¹ hg0i
    simpa [mul_assoc] using this
  have hcube : (g0 * s) ^ 3 = (g0⁻¹ * (g0⁻¹ * s * g0) * g0) * (g0⁻¹ * s * g0) * s := by
    have e : (g0 * s) ^ 3 = g0 ^ 3 * ((g0⁻¹ * (g0⁻¹ * s * g0) * g0) * (g0⁻¹ * s * g0) * s) := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hg03, one_mul]
  have hQ3 : (v * m.ψ mA) ^ 3 ∈ ascQ (c.u' * z) := by
    rw [hh, hcube, hqSub]
    exact mul_mem (mul_mem hc2 hc1) hsq
  have hord : orderOf g0 = 3 := orderOf_eq_prime hg03 hg01
  have hnQ : v * m.ψ mA ∉ ascQ (c.u' * z) := by
    intro hQ
    rw [hqSub] at hQ
    have hg0Q : g0 ∈ mb.qSub := by
      have : g0 = (v * m.ψ mA) * s⁻¹ := by rw [hh]; group
      rw [this]
      exact mul_mem hQ (inv_mem hsq)
    have h1 : orderOf (⟨g0, hg0Q⟩ : ↥mb.qSub) ∣ Nat.card ↥mb.qSub := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord, mb.card_qSub] at h1
    exact absurd h1 (by decide)
  exact mb.cube_cases hypb hhH hnQ hQ3

end AscCox

end CFSG.Quasithin
