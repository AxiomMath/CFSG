module

public import CFSG.Sporadic.SuzRecog.B0GluingLift
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public section

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.Sporadic.SuzOddCore


local notation "τ₀" => C1Model.tau0

section Identities

variable {P : Type*} [Group P]


private theorem conj_mul_conj_eq (a b x : P) : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  group

private theorem conj_conj_eq_of_twist {τ z t x : P} (hτz : τ * z * τ⁻¹ = z * t)
    (hzt : z * t = t * z) (ht : t * t = 1) :
    z * (τ * x * τ⁻¹) * z⁻¹ = t * (τ * (z * x * z⁻¹) * τ⁻¹) * t⁻¹ := by
  have e : τ * (z * x * z⁻¹) * τ⁻¹ = (τ * z * τ⁻¹) * (τ * x * τ⁻¹) * (τ * z * τ⁻¹)⁻¹ := by group
  have htzt : t * (z * t) = z := by rw [hzt, ← mul_assoc, ht, one_mul]
  rw [e, hτz]
  calc z * (τ * x * τ⁻¹) * z⁻¹ = (t * (z * t)) * (τ * x * τ⁻¹) * (t * (z * t))⁻¹ := by rw [htzt]
    _ = t * (z * t * (τ * x * τ⁻¹) * (z * t)⁻¹) * t⁻¹ := by group

private theorem mul_twist_of_sq {z t : P} (hz : z * z = 1) : z * (z * t) = t := by
  rw [← mul_assoc, hz, one_mul]

private theorem twist_mul_twist {τ z t : P} (hτz : τ * z * τ⁻¹ = z * t) (hτt : τ * t * τ⁻¹ = t)
    (hzt : z * t = t * z) (hz : z * z = 1) (ht : t * t = 1) :
    z * t * (τ * (z * t) * τ⁻¹) = t := by
  have e : τ * (z * t) * τ⁻¹ = (τ * z * τ⁻¹) * (τ * t * τ⁻¹) := by group
  rw [e, hτz, hτt, mul_assoc z t t, ht, mul_one, hzt, mul_assoc, hz, mul_one]

end Identities

theorem tau0_comm_t1 : τ₀ * suzInv 1 = suzInv 1 * τ₀ :=
  (C1Model.mem_invE_iff.1 C1Model.tau0_mem_invE).1

theorem tau0_conj_conj (x : Equiv.Perm (Fin 1782)) : τ₀ * (τ₀ * x * τ₀⁻¹) * τ₀⁻¹ = x :=
  conj_conj_of_mul_self C1Model.tau0_mul_self

theorem exists_tau_compat {G : Type*} [Group G]
    (α : ↥C1Model.J0 →* G) (hα : Function.Injective α) (τ' : G) (hτ2 : τ' * τ' = 1)
    (hnorm : ∀ x : ↥C1Model.J0, ∃ y : ↥C1Model.J0, τ' * α x * τ'⁻¹ = α y)
    (hT : ∀ x (hx : x ∈ C1Model.T0) (hx' : C1Model.tau0 * x * C1Model.tau0⁻¹ ∈ C1Model.J0),
      α ⟨_, hx'⟩ = τ' * α ⟨x, C1Model.T0_le_J0 hx⟩ * τ'⁻¹)
    (z₂ : Equiv.Perm (Fin 1782)) (hz₂ : z₂ ∈ C1Model.T0)
    (hz₂c : ∀ x ∈ C1Model.T0, z₂ * x = x * z₂) (hz₂2 : z₂ * z₂ = 1)
    (hτz : C1Model.tau0 * z₂ * C1Model.tau0⁻¹ = z₂ * suzInv 1)
    (ht₁ : suzInv 1 * C1Model.zJ0 ≠ C1Model.zJ0 * suzInv 1)
    (hcent : ∀ g ∈ ComponentClassification.PSL3Four.R,
      (∀ x (hx : x ∈ C1Model.T0),
        g * (C1Model.j0Equiv ⟨x, C1Model.T0_le_J0 hx⟩ : Equiv.Perm (Fin 42)) =
          (C1Model.j0Equiv ⟨x, C1Model.T0_le_J0 hx⟩ : Equiv.Perm (Fin 42)) * g) →
      ∃ w, ∃ hw : w ∈ C1Model.J0, (w = 1 ∨ w = suzInv 1 ∨ w = z₂ ∨ w = z₂ * suzInv 1) ∧
        g = (C1Model.j0Equiv ⟨w, hw⟩ : Equiv.Perm (Fin 42))) :
    ∃ α' : ↥C1Model.J0 →* G,
      (∀ x (hx : x ∈ C1Model.T0), α' ⟨x, C1Model.T0_le_J0 hx⟩ = α ⟨x, C1Model.T0_le_J0 hx⟩) ∧
      (∀ x, ∃ y, α' x = α y) ∧
      ∀ x (hx : x ∈ C1Model.J0) (hx' : C1Model.tau0 * x * C1Model.tau0⁻¹ ∈ C1Model.J0),
        α' ⟨_, hx'⟩ = τ' * α' ⟨x, hx⟩ * τ'⁻¹ := by
  classical
  have hτ'i : τ'⁻¹ = τ' := inv_eq_of_mul_eq_one_right hτ2
  let F : ↥C1Model.J0 → ↥C1Model.J0 := fun x => ⟨τ₀ * x * τ₀⁻¹, tau0_conj_mem_J0 x.2⟩
  have F_mul : ∀ x y, F (x * y) = F x * F y := fun x y => Subtype.ext (by
    show τ₀ * (x * y : Equiv.Perm (Fin 1782)) * τ₀⁻¹ = (τ₀ * x * τ₀⁻¹) * (τ₀ * y * τ₀⁻¹)
    exact conj_mul_conj _ _ _)
  have F_F : ∀ x, F (F x) = x := fun x => Subtype.ext (tau0_conj_conj x)
  let d : ↥C1Model.J0 → ↥C1Model.J0 := fun x => Classical.choose (hnorm (F x))
  have hd : ∀ x, α (d x) = τ' * α (F x) * τ'⁻¹ := fun x =>
    (Classical.choose_spec (hnorm (F x))).symm
  have d_mul : ∀ x y, d (x * y) = d x * d y := by
    intro x y
    apply hα
    rw [map_mul, hd, hd, hd, F_mul, map_mul]
    group
  have d_inj : Function.Injective d := by
    intro x y h
    have e := congrArg α h
    rw [hd, hd] at e
    have e2 : α (F x) = α (F y) := by
      have := congrArg (fun g => τ'⁻¹ * g * τ') e
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    have e3 := congrArg F (hα e2)
    rwa [F_F, F_F] at e3
  let δ : ↥C1Model.J0 →* ↥C1Model.J0 := MonoidHom.mk' d d_mul
  have hδbij : Function.Bijective δ := ⟨d_inj, Finite.surjective_of_injective d_inj⟩
  let δ' : ↥C1Model.J0 ≃* ↥C1Model.J0 := MulEquiv.ofBijective δ hδbij
  let γ : MulAut ↥ComponentClassification.PSL3Four.S :=
    (C1Model.j0Equiv.symm.trans δ').trans C1Model.j0Equiv
  obtain ⟨g, hg⟩ := ComponentClassification.PSL3Four.conjAutS_surjective γ
  have hgγ : ∀ s : ↥ComponentClassification.PSL3Four.S,
      (g : Equiv.Perm (Fin 42)) * s * (g : Equiv.Perm (Fin 42))⁻¹ =
        (γ s : Equiv.Perm (Fin 42)) := by
    intro s
    rw [← ComponentClassification.PSL3Four.conjAutS_apply, hg]
  have hγ : ∀ x : ↥C1Model.J0, γ (C1Model.j0Equiv x) = C1Model.j0Equiv (d x) := by
    intro x
    show C1Model.j0Equiv (δ' (C1Model.j0Equiv.symm (C1Model.j0Equiv x))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hdT : ∀ x (hx : x ∈ C1Model.T0), d ⟨x, C1Model.T0_le_J0 hx⟩ = ⟨x, C1Model.T0_le_J0 hx⟩ := by
    intro x hx
    apply hα
    rw [hd]
    have h := hT x hx (tau0_conj_mem_J0 (C1Model.T0_le_J0 hx))
    have e : F ⟨x, C1Model.T0_le_J0 hx⟩ = ⟨_, tau0_conj_mem_J0 (C1Model.T0_le_J0 hx)⟩ := rfl
    rw [e, h, hτ'i, ← mul_assoc, ← mul_assoc, hτ2, one_mul, mul_assoc, hτ2, mul_one]
  have hgT : ∀ x (hx : x ∈ C1Model.T0),
      (g : Equiv.Perm (Fin 42)) * (C1Model.j0Equiv ⟨x, C1Model.T0_le_J0 hx⟩ : Equiv.Perm (Fin 42)) =
        (C1Model.j0Equiv ⟨x, C1Model.T0_le_J0 hx⟩ : Equiv.Perm (Fin 42)) * g := by
    intro x hx
    have h := hgγ (C1Model.j0Equiv ⟨x, C1Model.T0_le_J0 hx⟩)
    rw [hγ, hdT x hx] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  obtain ⟨w, hw, hw4, hgw⟩ := hcent g g.2 hgT
  let wJ : ↥C1Model.J0 := ⟨w, hw⟩
  have hdw : ∀ x, d x = wJ * x * wJ⁻¹ := by
    intro x
    apply C1Model.j0Equiv.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hγ,
      ← hgγ, hgw]
  have E1 : ∀ x, τ' * α (F x) * τ'⁻¹ = α (wJ * x * wJ⁻¹) := fun x => by rw [← hd, hdw]
  have hFi : ∀ y : ↥C1Model.J0, F y⁻¹ = (F y)⁻¹ := by
    intro y
    rw [eq_inv_iff_mul_eq_one, ← F_mul, inv_mul_cancel]
    exact Subtype.ext (by
      show τ₀ * (1 : Equiv.Perm (Fin 1782)) * τ₀⁻¹ = 1
      rw [mul_one, mul_inv_cancel])
  have hcentral : ∀ x : ↥C1Model.J0, (wJ * F wJ) * x * (wJ * F wJ)⁻¹ = x := by
    intro x
    apply hα
    have e1 : τ' * α (wJ * F x * wJ⁻¹) * τ'⁻¹ = α (wJ * F (wJ * F x * wJ⁻¹) * wJ⁻¹) := by
      have := E1 (F (wJ * F x * wJ⁻¹))
      rwa [F_F] at this
    have e2 : α x = τ' * α (wJ * F x * wJ⁻¹) * τ'⁻¹ := by
      have := E1 (F x)
      rw [F_F] at this
      rw [← this, hτ'i, ← mul_assoc, ← mul_assoc, hτ2, one_mul, mul_assoc, hτ2, mul_one]
    rw [e2, e1, F_mul, F_mul, F_F, hFi, conj_mul_conj_eq]
  have hz2J : z₂ ∈ C1Model.J0 := C1Model.T0_le_J0 hz₂
  have ht1sq : suzInv 1 * suzInv 1 = 1 := suzInv_sq (by norm_num)
  have hz2t : z₂ * suzInv 1 = suzInv 1 * z₂ :=
    (C1Model.mem_invE_iff.1 (C1Model.T0_le_invE hz₂)).1
  have hFt : τ₀ * suzInv 1 * τ₀⁻¹ = suzInv 1 := by
    rw [tau0_comm_t1, mul_inv_cancel_right]
  have hnc : ∀ c : ↥C1Model.J0, (c : Equiv.Perm (Fin 1782)) = suzInv 1 →
      ¬ ∀ x : ↥C1Model.J0, c * x * c⁻¹ = x := by
    intro c hc h
    have e := congrArg Subtype.val (h ⟨C1Model.zJ0, C1Model.zJ0_mem_J0⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc] at e
    exact ht₁ (mul_inv_eq_iff_eq_mul.1 e)
  rcases hw4 with h1 | h1 | h1 | h1
  ·
    refine ⟨α, fun x hx => rfl, fun x => ⟨x, rfl⟩, fun x hx hx' => ?_⟩
    have h := E1 ⟨x, hx⟩
    have e1 : wJ * ⟨x, hx⟩ * wJ⁻¹ = ⟨x, hx⟩ := by
      have : wJ = 1 := Subtype.ext h1
      rw [this, one_mul, inv_one, mul_one]
    rw [e1] at h
    calc α ⟨_, hx'⟩ = α (F ⟨x, hx⟩) := rfl
      _ = τ' * (τ' * α (F ⟨x, hx⟩) * τ'⁻¹) * τ'⁻¹ := (conj_conj_of_mul_self hτ2).symm
      _ = τ' * α ⟨x, hx⟩ * τ'⁻¹ := by rw [h]
  ·
    let zJ : ↥C1Model.J0 := ⟨z₂, hz2J⟩
    refine ⟨α.comp (MulAut.conj zJ).toMonoidHom, fun x hx => ?_, fun x => ⟨zJ * x * zJ⁻¹, rfl⟩,
      fun x hx hx' => ?_⟩
    · show α (zJ * ⟨x, C1Model.T0_le_J0 hx⟩ * zJ⁻¹) = α ⟨x, C1Model.T0_le_J0 hx⟩
      congr 1
      apply Subtype.ext
      show z₂ * x * z₂⁻¹ = x
      rw [hz₂c x hx, mul_inv_cancel_right]
    · show α (zJ * ⟨τ₀ * x * τ₀⁻¹, hx'⟩ * zJ⁻¹) = τ' * α (zJ * ⟨x, hx⟩ * zJ⁻¹) * τ'⁻¹
      have e1 : τ' * α (zJ * ⟨x, hx⟩ * zJ⁻¹) * τ'⁻¹ =
          α (wJ * F (zJ * ⟨x, hx⟩ * zJ⁻¹) * wJ⁻¹) := by
        have := E1 (F (zJ * ⟨x, hx⟩ * zJ⁻¹))
        rwa [F_F] at this
      rw [e1]
      congr 1
      apply Subtype.ext
      show z₂ * (τ₀ * x * τ₀⁻¹) * z₂⁻¹ = w * (τ₀ * (z₂ * x * z₂⁻¹) * τ₀⁻¹) * w⁻¹
      rw [h1]
      exact conj_conj_eq_of_twist hτz hz2t ht1sq
  ·
    refine absurd hcentral (hnc _ ?_)
    show w * (τ₀ * w * τ₀⁻¹) = suzInv 1
    rw [h1, hτz, mul_twist_of_sq hz₂2]
  ·
    refine absurd hcentral (hnc _ ?_)
    show w * (τ₀ * w * τ₀⁻¹) = suzInv 1
    rw [h1]
    exact twist_mul_twist hτz hFt hz2t hz₂2 ht1sq

end CFSG.Sporadic.SuzRecog.B0Gluing
