module

public import Mathlib.GroupTheory.GroupAction.ConjAct

import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

variable {Q₁ Q₂ P : Type*} [Group Q₁] [Group Q₂] [Group P]

abbrev OuterActionPair (π₁ : Q₁ →* P) (π₂ : Q₂ →* P) (θ : π₁.ker ≃* π₂.ker) (q₁ : Q₁)
    (q₂ : Q₂) : Prop :=
  π₂ q₂ = π₁ q₁ ∧ ∀ x : π₁.ker, MulAut.conjNormal q₂ (θ x) = θ (MulAut.conjNormal q₁ x)

namespace OuterActionPair

variable {π₁ : Q₁ →* P} {π₂ : Q₂ →* P} {θ : π₁.ker ≃* π₂.ker} {q₁ q₁' : Q₁} {q₂ q₂' : Q₂}

theorem iff_mul_mul_inv :
    OuterActionPair π₁ π₂ θ q₁ q₂ ↔ π₂ q₂ = π₁ q₁ ∧ ∀ x : π₁.ker,
      q₂ * ((θ x : π₂.ker) : Q₂) * q₂⁻¹ = ((θ (MulAut.conjNormal q₁ x) : π₂.ker) : Q₂) := by
  refine and_congr_right fun _ => forall_congr' fun x => ?_
  rw [← MulAut.conjNormal_apply]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem one : OuterActionPair π₁ π₂ θ 1 1 := ⟨by simp, fun x => by simp⟩

theorem mul (h : OuterActionPair π₁ π₂ θ q₁ q₂) (h' : OuterActionPair π₁ π₂ θ q₁' q₂') :
    OuterActionPair π₁ π₂ θ (q₁ * q₁') (q₂ * q₂') := by
  refine ⟨by rw [map_mul, map_mul, h.1, h'.1], fun x => ?_⟩
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h'.2 x, h.2]

theorem inv (h : OuterActionPair π₁ π₂ θ q₁ q₂) : OuterActionPair π₁ π₂ θ q₁⁻¹ q₂⁻¹ := by
  refine ⟨by rw [map_inv, map_inv, h.1], fun x => ?_⟩
  have h1 : MulAut.conjNormal q₂ (θ (MulAut.conjNormal q₁⁻¹ x)) = θ x := by
    rw [h.2, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h2 := congrArg (MulAut.conjNormal q₂⁻¹) h1
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
  exact h2.symm

theorem of_ker (x : π₁.ker) : OuterActionPair π₁ π₂ θ (x : Q₁) ((θ x : π₂.ker) : Q₂) := by
  refine ⟨?_, fun y => ?_⟩
  · rw [(θ x).2, x.2]
  · rw [MulAut.conjNormal_val, MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv]

theorem unique (hZ₂ : center π₂.ker = ⊥) (h : OuterActionPair π₁ π₂ θ q₁ q₂)
    (h' : OuterActionPair π₁ π₂ θ q₁ q₂') : q₂ = q₂' := by
  have hd : q₂⁻¹ * q₂' ∈ π₂.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h.1, h'.1, inv_mul_cancel]
  have hc : (⟨q₂⁻¹ * q₂', hd⟩ : π₂.ker) ∈ center π₂.ker := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conjNormal q₂ g = MulAut.conjNormal q₂' g := by
      have e1 := h.2 (θ.symm g)
      have e2 := h'.2 (θ.symm g)
      rw [MulEquiv.apply_symm_apply] at e1 e2
      exact e1.trans e2.symm
    have h2 : MulAut.conjNormal (q₂⁻¹ * q₂') g = g := by
      rw [map_mul, MulAut.mul_apply, ← h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, MulAut.one_apply]
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    apply Subtype.ext
    change (g : Q₂) * (q₂⁻¹ * q₂') = (q₂⁻¹ * q₂') * (g : Q₂)
    calc (g : Q₂) * (q₂⁻¹ * q₂') = (q₂⁻¹ * q₂' * g * (q₂⁻¹ * q₂')⁻¹) * (q₂⁻¹ * q₂') := by
          rw [h3]
      _ = (q₂⁻¹ * q₂') * (g : Q₂) := by group
  rw [hZ₂, Subgroup.mem_bot] at hc
  have := congrArg Subtype.val hc
  exact inv_mul_eq_one.mp this

theorem of_hom {ψ : Q₁ →* Q₂} (hψ : ∀ x : π₁.ker, ψ x = θ x) (hπ : ∀ q, π₂ (ψ q) = π₁ q)
    (q : Q₁) : OuterActionPair π₁ π₂ θ q (ψ q) := by
  refine ⟨hπ q, fun x => ?_⟩
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, ← hψ x, ← hψ (MulAut.conjNormal q x), MulAut.conjNormal_apply,
    map_mul, map_mul, map_inv]

end OuterActionPair

variable {π₁ : Q₁ →* P} {π₂ : Q₂ →* P} {θ : π₁.ker ≃* π₂.ker}

def hasPartner (π₁ : Q₁ →* P) (π₂ : Q₂ →* P) (θ : π₁.ker ≃* π₂.ker) : Subgroup Q₁ where
  carrier := {q₁ | ∃ q₂ : Q₂, OuterActionPair π₁ π₂ θ q₁ q₂}
  mul_mem' := by
    rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, ha.mul hb⟩
  one_mem' := ⟨1, OuterActionPair.one⟩
  inv_mem' := by
    rintro _ ⟨a, ha⟩
    exact ⟨a⁻¹, ha.inv⟩

theorem exists_pair_of_closure {S : Set Q₁} (hS : Subgroup.closure S = ⊤)
    (h : ∀ q₁ ∈ S, ∃ q₂ : Q₂, OuterActionPair π₁ π₂ θ q₁ q₂) (q₁ : Q₁) :
    ∃ q₂ : Q₂, OuterActionPair π₁ π₂ θ q₁ q₂ := by
  have hle : Subgroup.closure S ≤ hasPartner π₁ π₂ θ := Subgroup.closure_le _ |>.mpr h
  rw [hS] at hle
  exact hle (Subgroup.mem_top q₁)

variable (π₁ π₂ θ)

theorem exists_mulEquiv_of_outer_action (hπ₁ : Function.Surjective π₁)
    (hZ₁ : center π₁.ker = ⊥) (hZ₂ : center π₂.ker = ⊥)
    (h : ∀ q₁ : Q₁, ∃ q₂ : Q₂, OuterActionPair π₁ π₂ θ q₁ q₂) :
    ∃ ψ : Q₁ ≃* Q₂, (∀ x : π₁.ker, ψ x = θ x) ∧ ∀ q, π₂ (ψ q) = π₁ q := by
  classical
  choose f hf using h
  have hmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    OuterActionPair.unique hZ₂ (hf (a * b)) ((hf a).mul (hf b))
  let ψ₀ : Q₁ →* Q₂ := MonoidHom.mk' f hmul
  have hψπ : ∀ q, π₂ (ψ₀ q) = π₁ q := fun q => (hf q).1
  have hψθ : ∀ x : π₁.ker, ψ₀ x = θ x := fun x =>
    OuterActionPair.unique hZ₂ (hf x) (OuterActionPair.of_ker x)
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hk : q ∈ π₁.ker := by
      rw [MonoidHom.mem_ker, ← hψπ q, hq, map_one]
    have hc : (⟨q, hk⟩ : π₁.ker) ∈ center π₁.ker := by
      rw [Subgroup.mem_center_iff]
      intro g
      have e := (hf q).2 g
      have hf1 : f q = 1 := hq
      rw [hf1, map_one, MulAut.one_apply] at e
      have e' := θ.injective e
      have e'' := congrArg Subtype.val e'
      rw [MulAut.conjNormal_apply] at e''
      apply Subtype.ext
      change (g : Q₁) * q = q * (g : Q₁)
      calc (g : Q₁) * q = (q * g * q⁻¹) * q := by rw [← e'']
        _ = q * (g : Q₁) := by group
    rw [hZ₁, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hsurj : Function.Surjective ψ₀ := by
    intro y
    obtain ⟨q₁, hq₁⟩ := hπ₁ (π₂ y)
    have hd : (ψ₀ q₁)⁻¹ * y ∈ π₂.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψπ, hq₁, inv_mul_cancel]
    refine ⟨q₁ * (θ.symm ⟨_, hd⟩ : π₁.ker), ?_⟩
    rw [map_mul, hψθ, MulEquiv.apply_symm_apply]
    simp
  exact ⟨MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩, hψθ, hψπ⟩

theorem exists_mulEquiv_of_outer_action_of_closure (hπ₁ : Function.Surjective π₁)
    (hZ₁ : center π₁.ker = ⊥) (hZ₂ : center π₂.ker = ⊥) {S : Set Q₁}
    (hS : Subgroup.closure S = ⊤)
    (h : ∀ q₁ ∈ S, ∃ q₂ : Q₂, OuterActionPair π₁ π₂ θ q₁ q₂) :
    ∃ ψ : Q₁ ≃* Q₂, (∀ x : π₁.ker, ψ x = θ x) ∧ ∀ q, π₂ (ψ q) = π₁ q :=
  exists_mulEquiv_of_outer_action π₁ π₂ θ hπ₁ hZ₁ hZ₂ (exists_pair_of_closure hS h)

theorem hom_ext_of_extends (hZ₂ : center π₂.ker = ⊥) {ψ ψ' : Q₁ →* Q₂}
    (hψ : ∀ x : π₁.ker, ψ x = θ x) (hψ' : ∀ x : π₁.ker, ψ' x = θ x)
    (hπ : ∀ q, π₂ (ψ q) = π₁ q) (hπ' : ∀ q, π₂ (ψ' q) = π₁ q) : ψ = ψ' :=
  MonoidHom.ext fun q => OuterActionPair.unique hZ₂ (OuterActionPair.of_hom hψ hπ q)
    (OuterActionPair.of_hom hψ' hπ' q)

end CFSG.Sporadic.Recognition.LyonsSims
