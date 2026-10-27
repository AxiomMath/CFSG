module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

namespace Row21

variable {X : Type*} [Group X]

theorem eq_one_of_sq_eq_one {V : Subgroup X} (hodd : Odd (Nat.card V)) {v : X} (hv : v ∈ V)
    (h : v ^ 2 = 1) : v = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : v ^ Nat.card V = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨v, hv⟩ : V)))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [hk] at h1
  have h2 : v ^ (2 * k + 1) = v := by rw [pow_succ, pow_mul, h, one_pow, one_mul]
  rw [← h2]
  exact h1

theorem exists_mul_self_eq_inv {V : Subgroup X} (hodd : Odd (Nat.card V)) {w : X} (hw : w ∈ V) :
    ∃ u ∈ V, u * u = w⁻¹ := by
  obtain ⟨k, hk⟩ := hodd
  have h1 : w ^ Nat.card V = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨w, hw⟩ : V)))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [hk] at h1
  refine ⟨(w ^ (k + 1))⁻¹, V.inv_mem (V.pow_mem hw _), ?_⟩
  have h2 : w ^ (k + 1) * w ^ (k + 1) = w := by
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, h1, one_mul]
  rw [← mul_inv_rev, h2]

theorem map_mem_of_odd_complement {V B : Subgroup X} [V.Normal] (hodd : Odd (Nat.card V))
    (hfact : ∀ x : X, ∃ b ∈ B, ∃ v ∈ V, x = b * v) (hBV : ∀ x ∈ B, x ∈ V → x = 1)
    {z e : X} (hzc : ∀ b ∈ B, z * b = b * z) (hzinv : ∀ v ∈ V, z * v * z⁻¹ = v⁻¹)
    (heB : e ∈ B) (hec : ∀ v ∈ V, e * v * e⁻¹ = v → v = 1) (α : X →* X) (hαe : α e = e)
    (hαz : z⁻¹ * α z ∈ V) : ∀ b ∈ B, α b ∈ B := by
  obtain ⟨u, hu, huz⟩ : ∃ u ∈ V, u * z * u⁻¹ = α z := by
    obtain ⟨u, hu, hu2⟩ := exists_mul_self_eq_inv hodd hαz
    refine ⟨u, hu, ?_⟩
    calc u * z * u⁻¹ = u * (z * u⁻¹ * z⁻¹) * z := by group
      _ = u * u * z := by rw [hzinv _ (V.inv_mem hu), inv_inv]
      _ = (z * (z⁻¹ * α z) * z⁻¹) * z := by rw [hu2, ← hzinv _ hαz]
      _ = α z := by group
  have key : ∀ b ∈ B, u⁻¹ * α b * u ∈ B := by
    intro b hb
    have hyc : α b * α z = α z * α b := by
      rw [← map_mul, ← map_mul, ← hzc b hb]
    rw [← huz] at hyc
    have e1 : (u⁻¹ * α b * u) * z = z * (u⁻¹ * α b * u) := by
      calc (u⁻¹ * α b * u) * z = u⁻¹ * (α b * (u * z * u⁻¹)) * u := by group
        _ = u⁻¹ * (u * z * u⁻¹ * α b) * u := by rw [hyc]
        _ = z * (u⁻¹ * α b * u) := by group
    obtain ⟨b', hb', v', hv', hy'⟩ := hfact (u⁻¹ * α b * u)
    have h1 : b' * (v' * z) = b' * (z * v') := by
      calc b' * (v' * z) = (b' * v') * z := by group
        _ = z * (b' * v') := by rw [← hy']; exact e1
        _ = (z * b') * v' := by group
        _ = (b' * z) * v' := by rw [hzc b' hb']
        _ = b' * (z * v') := by group
    have h2 : v' * z = z * v' := mul_left_cancel h1
    have h3 : v'⁻¹ = v' := by
      rw [← hzinv v' hv']
      calc z * v' * z⁻¹ = v' * z * z⁻¹ := by rw [← h2]
        _ = v' := by group
    have h4 : v' = 1 := eq_one_of_sq_eq_one hodd hv' (by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h3.symm)
    rw [hy', h4, mul_one]
    exact hb'
  have hu1 : u = 1 := by
    have h1 := key e heB
    rw [hαe] at h1
    have h2 : u⁻¹ * e * u * e⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem heB)
    have h3 : u⁻¹ * e * u * e⁻¹ ∈ V := by
      have : u⁻¹ * e * u * e⁻¹ = u⁻¹ * (e * u * e⁻¹) := by group
      rw [this]
      exact V.mul_mem (V.inv_mem hu) (Subgroup.Normal.conj_mem ‹V.Normal› u hu e)
    have h4 := hBV _ h2 h3
    have h5 : e * u * e⁻¹ = u := by
      have : u⁻¹ * (e * u * e⁻¹) = 1 := by rw [← h4]; group
      exact (inv_mul_eq_one.mp this).symm
    exact hec u hu h5
  intro b hb
  have := key b hb
  rwa [hu1, inv_one, one_mul, mul_one] at this

end Row21

end Stellmacher.L3YC

end CFSG.Quasithin
