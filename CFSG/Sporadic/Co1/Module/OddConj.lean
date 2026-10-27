module

public import CFSG.Sporadic.Co1.Module.OddGroup

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open MulAction

section Conj

variable {G Ω : Type*} [Group G] [MulAction G Ω]

omit [MulAction G Ω] in
theorem comm_conj_iff (x c r : G) :
    c * r = r * c ↔ (x * c * x⁻¹) * (x * r * x⁻¹) = (x * r * x⁻¹) * (x * c * x⁻¹) := by
  constructor
  · intro h
    calc (x * c * x⁻¹) * (x * r * x⁻¹) = x * (c * r) * x⁻¹ := by group
      _ = x * (r * c) * x⁻¹ := by rw [h]
      _ = (x * r * x⁻¹) * (x * c * x⁻¹) := by group
  · intro h
    have h2 : x * (c * r) * x⁻¹ = x * (r * c) * x⁻¹ := by
      calc x * (c * r) * x⁻¹ = (x * c * x⁻¹) * (x * r * x⁻¹) := by group
        _ = (x * r * x⁻¹) * (x * c * x⁻¹) := h
        _ = x * (r * c) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

omit [MulAction G Ω] in
theorem comm_of_mem_centralizer {r z : G} (hz : z ∈ Subgroup.centralizer ({r} : Set G)) :
    z * r = r * z := by
  have := Subgroup.mem_centralizer_singleton_iff.1 hz
  exact this

omit [MulAction G Ω] in
theorem conj_eq_of_mem_centralizer {r z : G} (hz : z ∈ Subgroup.centralizer ({r} : Set G)) :
    z * r * z⁻¹ = r := by
  have hz' := comm_of_mem_centralizer hz
  calc z * r * z⁻¹ = r * z * z⁻¹ := by rw [hz']
    _ = r := by group

omit [MulAction G Ω] in
theorem card_centralizer_inf_conj (x r s : G) :
    Nat.card ↥(Subgroup.centralizer ({x * r * x⁻¹} : Set G) ⊓
        Subgroup.centralizer {x * s * x⁻¹}) =
      Nat.card ↥(Subgroup.centralizer ({r} : Set G) ⊓ Subgroup.centralizer {s}) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj x).toEquiv (fun c => ?_))).symm
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  show (c * r = r * c ∧ c * s = s * c) ↔
    ((x * c * x⁻¹) * (x * r * x⁻¹) = (x * r * x⁻¹) * (x * c * x⁻¹) ∧
      (x * c * x⁻¹) * (x * s * x⁻¹) = (x * s * x⁻¹) * (x * c * x⁻¹))
  rw [comm_conj_iff x c r, comm_conj_iff x c s]

omit [MulAction G Ω] in
theorem mem_centralizer_conj_iff (x r g : G) :
    g ∈ Subgroup.centralizer ({x * r * x⁻¹} : Set G) ↔
      x⁻¹ * g * x ∈ Subgroup.centralizer ({r} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have h := comm_conj_iff x (x⁻¹ * g * x) r
  rw [show x * (x⁻¹ * g * x) * x⁻¹ = g by group] at h
  exact h.symm

omit [MulAction G Ω] in
theorem isConj_conj_iff (x r s : G) : IsConj (x * r * x⁻¹) (x * s * x⁻¹) ↔ IsConj r s := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨x⁻¹ * c * x, ?_⟩
    calc x⁻¹ * c * x * r * (x⁻¹ * c * x)⁻¹ = x⁻¹ * (c * (x * r * x⁻¹) * c⁻¹) * x := by group
      _ = x⁻¹ * (x * s * x⁻¹) * x := by rw [hc]
      _ = s := by group
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨x * c * x⁻¹, ?_⟩
    calc x * c * x⁻¹ * (x * r * x⁻¹) * (x * c * x⁻¹)⁻¹ = x * (c * r * c⁻¹) * x⁻¹ := by group
      _ = x * s * x⁻¹ := by rw [hc]

omit [MulAction G Ω] in
theorem conj_ne_iff (x r s : G) : x * s * x⁻¹ ≠ x * r * x⁻¹ ↔ s ≠ r := by
  constructor
  · intro h e
    exact h (by rw [e])
  · intro h e
    exact h (mul_left_cancel (mul_right_cancel e))

omit [MulAction G Ω] in
theorem orderOf_conj_pair (x r s : G) :
    orderOf (x * r * x⁻¹ * (x * s * x⁻¹)) = orderOf (r * s) := by
  have : x * r * x⁻¹ * (x * s * x⁻¹) = x * (r * s) * x⁻¹ := by group
  rw [this, orderOf_conj']

theorem mem_fix_conj_iff (x r : G) (ω : Ω) : (x * r * x⁻¹) • ω = ω ↔ r • x⁻¹ • ω = x⁻¹ • ω := by
  rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul]

theorem smul_fix_conj_iff (x r : G) (v : Ω) : (x * r * x⁻¹) • x • v = x • v ↔ r • v = v := by
  rw [mem_fix_conj_iff, inv_smul_smul]

theorem smul_mem_orbit_iff' (x : G) (ω₀ v : Ω) : x • v ∈ orbit G ω₀ ↔ v ∈ orbit G ω₀ := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨x⁻¹ * h, ?_⟩
    show (x⁻¹ * h) • ω₀ = v
    rw [mul_smul]
    have : h • ω₀ = x • v := hh
    rw [this, inv_smul_smul]
  · rintro ⟨h, hh⟩
    refine ⟨x * h, ?_⟩
    show (x * h) • ω₀ = x • v
    rw [mul_smul]
    have : h • ω₀ = v := hh
    rw [this]

end Conj

end CFSG.Sporadic.Co1.Module.Odd
