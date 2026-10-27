module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped IsMulCommutative commutatorElement

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[expose] def fixSpaceOf {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.ker ((g : V →ₗ[F] V) - LinearMap.id)

theorem mem_fixSpaceOf {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : V ≃ₗ[F] V) (v : V) : v ∈ fixSpaceOf g ↔ g v = v := by
  simp [fixSpaceOf, sub_eq_zero]

@[expose] def fixSpace {F K V : Type} [Field F] [Group K] [AddCommGroup V] [Module F V]
    (ρ : K →* (V ≃ₗ[F] V)) (t : K) : Submodule F V :=
  fixSpaceOf (ρ t)

theorem mem_fixSpace {F K V : Type} [Field F] [Group K] [AddCommGroup V] [Module F V]
    (ρ : K →* (V ≃ₗ[F] V)) (t : K) (v : V) : v ∈ fixSpace ρ t ↔ ρ t v = v :=
  mem_fixSpaceOf _ _

@[expose] def FixBound {F K V : Type} [Field F] [Group K] [AddCommGroup V] [Module F V]
    (ρ : K →* (V ≃ₗ[F] V)) (r : ℕ) : Prop :=
  ∀ t : K, t ≠ 1 → IsPGroup 2 (Subgroup.zpowers t) →
    Module.finrank F (fixSpace ρ t) ≤ r

@[expose] def negOne (F V : Type) [Field F] [AddCommGroup V] [Module F V] : V ≃ₗ[F] V :=
  LinearEquiv.neg F

@[simp] theorem negOne_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V] (v : V) :
    negOne F V v = -v := rfl

@[expose] def IsIrreducibleRep {F K V : Type} [Field F] [Group K] [AddCommGroup V] [Module F V]
    (ρ : K →* (V ≃ₗ[F] V)) : Prop :=
  ∀ W : Submodule F V, (∀ k : K, ∀ w ∈ W, ρ k w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def NoInvariantAlt {F K V : Type} [Field F] [Group K] [AddCommGroup V] [Module F V]
    (ρ : K →* (V ≃ₗ[F] V)) : Prop :=
  ∀ f : V →ₗ[F] V →ₗ[F] F, (∀ v, f v v = 0) →
    (∀ (k : K) (v w : V), f (ρ k v) (ρ k w) = f v w) → f = 0

@[expose] def wt {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (χ : ↥E →* Fˣ) : Submodule F V where
  carrier := {v | ∀ e : ↥E, (e : V ≃ₗ[F] V) v = ((χ e : Fˣ) : F) • v}
  add_mem' := by
    intro a b ha hb e
    simp [ha e, hb e]
  zero_mem' := by
    intro e
    simp
  smul_mem' := by
    intro c v hv e
    simp [hv e, smul_comm c]

theorem mem_wt {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (E : Subgroup (V ≃ₗ[F] V)) (χ : ↥E →* Fˣ) (v : V) :
    v ∈ wt E χ ↔ ∀ e : ↥E, (e : V ≃ₗ[F] V) v = ((χ e : Fˣ) : F) • v :=
  Iff.rfl

@[expose] def SzSetup (K : Type) [Group K] (R : Subgroup K) [R.Normal] : Prop :=
  Group.IsPerfect K ∧ IsPGroup 2 R ∧ IsSz (K ⧸ R) 3

@[expose] noncomputable def chiefRepE {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    {N W₁ W₂ : Subgroup H}
    (hN₁ : N ≤ normalizer (W₁ : Set H)) (hN₂ : N ≤ normalizer (W₂ : Set H))
    [(W₂.subgroupOf W₁).Normal] [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)] :
    N →* (Additive (W₁ ⧸ W₂.subgroupOf W₁) ≃ₗ[ZMod p] Additive (W₁ ⧸ W₂.subgroupOf W₁)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
    (Additive (W₁ ⧸ W₂.subgroupOf W₁))).toMonoidHom.comp
      (CFSG.ABGLocalTools.chiefRep (p := p) hN₁ hN₂)

theorem chiefRepE_eq_one_iff {p : ℕ} [Fact p.Prime] {H : Type} [Group H] {N W₁ W₂ : Subgroup H}
    (hN₁ : N ≤ normalizer (W₁ : Set H)) (hN₂ : N ≤ normalizer (W₂ : Set H))
    [(W₂.subgroupOf W₁).Normal] [IsElementaryAbelian p (W₁ ⧸ W₂.subgroupOf W₁)] (n : N) :
    chiefRepE (p := p) hN₁ hN₂ n = 1 ↔ ∀ w ∈ W₁, ⁅w, (n : H)⁆ ∈ W₂ := by
  rw [← CFSG.ABGLocalTools.chiefRep_eq_one_iff (p := p) hN₁ hN₂ n]
  constructor
  · intro h
    have h' : (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
      (Additive (W₁ ⧸ W₂.subgroupOf W₁))) (CFSG.ABGLocalTools.chiefRep (p := p) hN₁ hN₂ n) = 1 := h
    exact (MulEquiv.map_eq_one_iff _).mp h'
  · intro h
    show (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
      (Additive (W₁ ⧸ W₂.subgroupOf W₁))) (CFSG.ABGLocalTools.chiefRep (p := p) hN₁ hN₂ n) = 1
    rw [h]
    exact map_one _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Sz5
