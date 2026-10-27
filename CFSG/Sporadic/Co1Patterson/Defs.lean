module

public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.Monster.GMS.TwoAGraph
public import CFSG.LargeExtraspecial.S14Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.Monster.GMS

noncomputable abbrev setting {X : Type} [Group X] [Finite X] {t : X}
    (h : PattersonCo1Hyp X t) : Setting X :=
  Setting.ofFStar t h.orderOf_eq h.extraspecial

@[expose] def NotWeaklyClosed {X : Type} [Group X] [Finite X] {t : X}
    (h : PattersonCo1Hyp X t) : Prop :=
  ∃ g : X, g * t * g⁻¹ ∈ (setting h).QG ∧ g * t * g⁻¹ ≠ t

@[expose] noncomputable def qOf {X : Type} [Group X] (w : X) : Subgroup X :=
  (timmesfeldFStar (centralizer ({w} : Set X))).map (centralizer ({w} : Set X)).subtype

@[expose] def qGraph {X : Type} [Group X] (t : X) : SimpleGraph (ConjVert t) where
  Adj x y := x ≠ y ∧ ((y : X) ∈ qOf (x : X) ∨ (x : X) ∈ qOf (y : X))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[expose] def commonQGraph {X : Type} [Group X] (t : X) : SimpleGraph (ConjVert t) where
  Adj x y := x ≠ y ∧ (x : X) * y = y * x ∧
    ∃ w : ConjVert t, (x : X) ∈ qOf (w : X) ∧ (y : X) ∈ qOf (w : X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, let ⟨w, h1, h2⟩ := h.2.2; ⟨w, h2, h1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[expose] noncomputable def q₀ : QuadraticForm (ZMod 2) (Fin 8 → ZMod 2) :=
  ∑ i : Fin 4, QuadraticMap.linMulLin (LinearMap.proj (Fin.castAdd 4 i))
    (LinearMap.proj (Fin.natAdd 4 i))

@[expose] noncomputable def bil₀ : (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) → ZMod 2 :=
  QuadraticMap.polar q₀

@[expose] noncomputable def L₀ : Subgroup ((Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) :=
  timmesfeldOmega q₀

structure ExtraspecialTypeSystem (n : ℕ) (L : Type) [Group L]
    (act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)))
    (qf : (Fin n → ZMod 2) → ZMod 2) (bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2)
    (H : Type) [Group H] where
  φ : H →* L
  φ_surj : Function.Surjective φ
  z : H
  vec : H → Fin n → ZMod 2
  z_mul_self : z * z = 1
  z_ne_one : z ≠ 1
  z_comm : ∀ c : H, c * z = z * c
  φ_z : φ z = 1
  vec_mul : ∀ p q, φ p = 1 → φ q = 1 → vec (p * q) = vec p + vec q
  vec_eq_zero : ∀ q, φ q = 1 → (vec q = 0 ↔ q = 1 ∨ q = z)
  vec_conj : ∀ c q, φ q = 1 → vec (c * q * c⁻¹) = act (φ c) (vec q)
  vec_surj : ∀ w, ∃ q, φ q = 1 ∧ vec q = w
  mul_self_eq_one_iff : ∀ q, φ q = 1 → (q * q = 1 ↔ qf (vec q) = 0)
  mul_self_eq_z_iff : ∀ q, φ q = 1 → (q * q = z ↔ qf (vec q) = 1)
  comm_eq_one_iff : ∀ p q, φ p = 1 → φ q = 1 →
    (p * q * p⁻¹ * q⁻¹ = 1 ↔ bil (vec p) (vec q) = 0)
  comm_eq_z_iff : ∀ p q, φ p = 1 → φ q = 1 →
    (p * q * p⁻¹ * q⁻¹ = z ↔ bil (vec p) (vec q) = 1)
  center_eq : ∀ q, φ q = 1 → (∀ p, φ p = 1 → p * q = q * p) → q = 1 ∨ q = z

end CFSG.Sporadic.Co1Patterson
