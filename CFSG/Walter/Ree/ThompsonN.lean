module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Walter.Ree

@[ext] structure ThompsonN (K : Type*) [Field K] (σ : K ≃+* K) where
  κ : Kˣ
  α : K
  β : K
  γ : K

variable {K : Type*} [Field K]

@[expose] def thompsonMul (σ : K ≃+* K) (x y : ThompsonN K σ) : ThompsonN K σ :=
  ⟨x.κ * y.κ, x.α * y.κ + y.α,
    x.β * (y.κ * σ y.κ) + y.β + x.α * y.κ * σ y.α - σ x.α * σ y.κ * y.α,
    y.γ + x.γ * (y.κ ^ 2 * σ y.κ) + y.α * x.β * (y.κ * σ y.κ) + σ x.α * σ y.κ * y.α ^ 2
      + x.α * y.κ * (y.α * σ y.α) - x.α ^ 2 * y.κ ^ 2 * σ y.α⟩

namespace ThompsonN

variable (σ : K ≃+* K) in
@[expose] def equivProd : ThompsonN K σ ≃ Kˣ × K × K × K where
  toFun x := (x.κ, x.α, x.β, x.γ)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (σ : K ≃+* K) in
theorem card [Finite K] : Nat.card (ThompsonN K σ) = Nat.card K ^ 3 * (Nat.card K - 1) := by
  rw [Nat.card_congr (equivProd σ), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_units]
  ring

theorem three_eq_zero [CharP K 3] : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

variable [CharP K 3] (σ : K ≃+* K)

instance instGroup : Group (ThompsonN K σ) where
  mul := thompsonMul σ
  mul_assoc x y z := by
    change thompsonMul σ (thompsonMul σ x y) z = thompsonMul σ x (thompsonMul σ y z)
    ext
    · simp [thompsonMul, mul_assoc]
    · simp only [thompsonMul, Units.val_mul]; ring
    · simp only [thompsonMul, Units.val_mul, map_add, map_mul]; ring
    · simp only [thompsonMul, Units.val_mul, map_add, map_mul]
      linear_combination (-(y.α * z.κ * (x.α * y.κ * z.κ * σ z.α + σ x.α * σ y.κ * z.α * σ z.κ)))
        * three_eq_zero (K := K)
  one := ⟨1, 0, 0, 0⟩
  one_mul x := by
    change thompsonMul σ ⟨1, 0, 0, 0⟩ x = x
    ext <;> simp [thompsonMul]
  mul_one x := by
    change thompsonMul σ x ⟨1, 0, 0, 0⟩ = x
    ext <;> simp [thompsonMul]
  inv x := ⟨x.κ⁻¹, -(x.α * (x.κ⁻¹ : Kˣ)), -(x.β * ((x.κ⁻¹ : Kˣ) * σ (x.κ⁻¹ : Kˣ))),
    (x.α * x.β - x.γ) * ((x.κ⁻¹ : Kˣ) ^ 2 * σ (x.κ⁻¹ : Kˣ))⟩
  inv_mul_cancel x := by
    change thompsonMul σ _ x = ⟨1, 0, 0, 0⟩
    have hk : (x.κ : K) ≠ 0 := x.κ.ne_zero
    have hsk : σ (x.κ : K) ≠ 0 := by simp
    ext
    · simp [thompsonMul]
    · simp [thompsonMul]
    · simp only [thompsonMul, Units.val_inv_eq_inv_val, map_inv₀, map_neg, map_mul]
      field_simp
      ring
    · simp only [thompsonMul, Units.val_inv_eq_inv_val, map_inv₀, map_neg, map_mul]
      field_simp
      linear_combination (-(x.α ^ 2 * σ x.α)) * three_eq_zero (K := K)

variable {σ}

theorem mul_def (x y : ThompsonN K σ) : x * y = thompsonMul σ x y := rfl

theorem one_def : (1 : ThompsonN K σ) = ⟨1, 0, 0, 0⟩ := rfl

theorem inv_def (x : ThompsonN K σ) :
    x⁻¹ = ⟨x.κ⁻¹, -(x.α * (x.κ⁻¹ : Kˣ)), -(x.β * ((x.κ⁻¹ : Kˣ) * σ (x.κ⁻¹ : Kˣ))),
      (x.α * x.β - x.γ) * ((x.κ⁻¹ : Kˣ) ^ 2 * σ (x.κ⁻¹ : Kˣ))⟩ := rfl

@[simp] theorem mul_κ (x y : ThompsonN K σ) : (x * y).κ = x.κ * y.κ := rfl

@[simp] theorem mul_α (x y : ThompsonN K σ) : (x * y).α = x.α * y.κ + y.α := rfl

theorem mul_β (x y : ThompsonN K σ) :
    (x * y).β = x.β * (y.κ * σ y.κ) + y.β + x.α * y.κ * σ y.α - σ x.α * σ y.κ * y.α := rfl

theorem mul_γ (x y : ThompsonN K σ) :
    (x * y).γ = y.γ + x.γ * (y.κ ^ 2 * σ y.κ) + y.α * x.β * (y.κ * σ y.κ)
      + σ x.α * σ y.κ * y.α ^ 2 + x.α * y.κ * (y.α * σ y.α) - x.α ^ 2 * y.κ ^ 2 * σ y.α := rfl

@[simp] theorem one_κ : (1 : ThompsonN K σ).κ = 1 := rfl

@[simp] theorem one_α : (1 : ThompsonN K σ).α = 0 := rfl

@[simp] theorem one_β : (1 : ThompsonN K σ).β = 0 := rfl

@[simp] theorem one_γ : (1 : ThompsonN K σ).γ = 0 := rfl

variable (σ) in
@[expose] def kappaHom : ThompsonN K σ →* Kˣ where
  toFun x := x.κ
  map_one' := rfl
  map_mul' _ _ := rfl

variable (σ) in
@[expose] def torus : Kˣ →* ThompsonN K σ where
  toFun κ := ⟨κ, 0, 0, 0⟩
  map_one' := rfl
  map_mul' κ l := by ext <;> simp [mul_def, thompsonMul]

@[simp] theorem torus_κ (κ : Kˣ) : (torus σ κ).κ = κ := rfl

@[simp] theorem torus_α (κ : Kˣ) : (torus σ κ).α = 0 := rfl

@[simp] theorem torus_β (κ : Kˣ) : (torus σ κ).β = 0 := rfl

@[simp] theorem torus_γ (κ : Kˣ) : (torus σ κ).γ = 0 := rfl

theorem kappaHom_comp_torus : (kappaHom σ).comp (torus σ) = MonoidHom.id Kˣ := rfl

theorem torus_injective : Function.Injective (torus σ) := fun κ l h => by
  simpa using congrArg ThompsonN.κ h

variable (σ) in
@[expose] def P : Subgroup (ThompsonN K σ) := (kappaHom σ).ker

variable (σ) in
@[expose] def R : Subgroup (ThompsonN K σ) := (torus σ).range

theorem mem_P {x : ThompsonN K σ} : x ∈ P σ ↔ x.κ = 1 := Iff.rfl

theorem mem_R {x : ThompsonN K σ} : x ∈ R σ ↔ x.α = 0 ∧ x.β = 0 ∧ x.γ = 0 := by
  constructor
  · rintro ⟨κ, rfl⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x.κ, by ext <;> simp [h1, h2, h3]⟩

instance P_normal : (P σ).Normal := MonoidHom.normal_ker _

@[expose] noncomputable def R_equiv : Kˣ ≃* R σ :=
  MonoidHom.ofInjective (torus_injective (σ := σ))

instance R_isCyclic [Finite K] : IsCyclic (R σ) :=
  isCyclic_of_surjective (R_equiv (σ := σ)).toMonoidHom (R_equiv (σ := σ)).surjective

theorem card_R [Finite K] : Nat.card (R σ) = Nat.card K - 1 := by
  rw [← Nat.card_congr (R_equiv (σ := σ)).toEquiv, Nat.card_units]

@[expose] def P_equiv : P σ ≃ K × K × K where
  toFun x := (x.1.α, x.1.β, x.1.γ)
  invFun x := ⟨⟨1, x.1, x.2.1, x.2.2⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨κ, α, β, γ⟩, hx⟩ := x
    have : κ = 1 := hx
    subst this
    rfl
  right_inv _ := rfl

theorem card_P [Finite K] : Nat.card (P σ) = Nat.card K ^ 3 := by
  rw [Nat.card_congr (P_equiv (σ := σ)), Nat.card_prod, Nat.card_prod]
  ring

theorem P_sup_R : P σ ⊔ R σ = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have h : x = (x * (torus σ x.κ)⁻¹) * torus σ x.κ := by group
  rw [h]
  refine Subgroup.mul_mem_sup ?_ ⟨x.κ, rfl⟩
  change (x * (torus σ x.κ)⁻¹).κ = 1
  simp [mul_def, thompsonMul, inv_def]

theorem P_inf_R : P σ ⊓ R σ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hP, hR⟩ := hx
  obtain ⟨h1, h2, h3⟩ := mem_R.1 hR
  have : x = 1 := by ext <;> simp_all [mem_P]
  exact this

theorem torus_conj (κ : Kˣ) (α β γ : K) :
    (torus σ κ)⁻¹ * ⟨1, α, β, γ⟩ * torus σ κ =
      ⟨1, α * κ, β * (κ * σ κ), γ * (κ ^ 2 * σ κ)⟩ := by
  have hk : (κ : K) ≠ 0 := κ.ne_zero
  ext
  · simp [mul_def, thompsonMul, inv_def]
  · simp [mul_def, thompsonMul, inv_def]
  · simp [mul_def, thompsonMul, inv_def]
  · simp [mul_def, thompsonMul, inv_def]

theorem eq_of_mem_P {x : ThompsonN K σ} (hx : x ∈ P σ) : x = ⟨1, x.α, x.β, x.γ⟩ := by
  ext <;> simp [mem_P.1 hx]

theorem mul_P (α β γ ξ η ζ : K) :
    (⟨1, α, β, γ⟩ : ThompsonN K σ) * ⟨1, ξ, η, ζ⟩ =
      ⟨1, α + ξ, β + η + α * σ ξ - σ α * ξ,
        ζ + γ + ξ * β + σ α * ξ ^ 2 + α * ξ * σ ξ - α ^ 2 * σ ξ⟩ := by
  ext
  · simp [mul_def, thompsonMul]
  · simp [mul_def, thompsonMul]
  · simp [mul_def, thompsonMul]
  · simp [mul_def, thompsonMul]
    ring

theorem inv_P (α β γ : K) : (⟨1, α, β, γ⟩ : ThompsonN K σ)⁻¹ = ⟨1, -α, -β, α * β - γ⟩ := by
  ext <;> simp [inv_def]

theorem commutator_P (α β γ ξ η ζ : K) :
    (⟨1, α, β, γ⟩ : ThompsonN K σ)⁻¹ * (⟨1, ξ, η, ζ⟩ : ThompsonN K σ)⁻¹ * ⟨1, α, β, γ⟩ *
        ⟨1, ξ, η, ζ⟩ =
      ⟨1, 0, σ α * ξ - α * σ ξ,
        α ^ 2 * σ ξ - α * η - α * σ α * ξ + α * σ ξ * ξ + β * ξ - σ α * ξ ^ 2⟩ := by
  rw [inv_P, inv_P, mul_P, mul_P, mul_P]
  ext
  · rfl
  · simp only; ring
  · simp only [map_add, map_neg]
    linear_combination (norm := skip)
    ring_nf
    reduce_mod_char!
  · simp only [map_add, map_neg]
    linear_combination (norm := skip)
    ring_nf
    reduce_mod_char!

theorem inv_mul_inv_mul_mul_eq_one_iff {G : Type*} [Group G] {x y : G} :
    x⁻¹ * y⁻¹ * x * y = 1 ↔ x * y = y * x := by
  constructor
  · intro h
    calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
      _ = y * x := by rw [h, mul_one]
  · intro h
    calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
      _ = x⁻¹ * y⁻¹ * (y * x) := by rw [h]
      _ = 1 := by group

variable (σ) in
@[expose] def P2 : Subgroup (ThompsonN K σ) where
  carrier := {x | x.κ = 1 ∧ x.α = 0}
  mul_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := fun {x} hx => ⟨by simp [inv_def, hx.1], by simp [inv_def, hx.2]⟩

variable (σ) in
@[expose] def Zc : Subgroup (ThompsonN K σ) where
  carrier := {x | x.κ = 1 ∧ x.α = 0 ∧ x.β = 0}
  mul_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1],
    by simp [mul_β, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]⟩
  one_mem' := ⟨rfl, rfl, rfl⟩
  inv_mem' := fun {x} hx => ⟨by simp [inv_def, hx.1], by simp [inv_def, hx.2.1],
    by simp [inv_def, hx.2.2]⟩

theorem mem_P2 {x : ThompsonN K σ} : x ∈ P2 σ ↔ x.κ = 1 ∧ x.α = 0 := Iff.rfl

theorem mem_Zc {x : ThompsonN K σ} : x ∈ Zc σ ↔ x.κ = 1 ∧ x.α = 0 ∧ x.β = 0 := Iff.rfl

theorem commutator_P_le : ⁅P σ, P σ⁆ ≤ P2 σ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  have hx' := eq_of_mem_P (P σ |>.inv_mem hx)
  have hy' := eq_of_mem_P (P σ |>.inv_mem hy)
  have e : x * y * x⁻¹ * y⁻¹ = x⁻¹⁻¹ * y⁻¹⁻¹ * x⁻¹ * y⁻¹ := by simp
  rw [e, hx', hy', commutator_P]
  exact ⟨rfl, rfl⟩

theorem Zc_le_commutator : Zc σ ≤ ⁅P σ, P σ⁆ := by
  intro x hx
  have e : x = (⟨1, 0, x.γ, 0⟩ : ThompsonN K σ)⁻¹ * (⟨1, 1, 0, 0⟩ : ThompsonN K σ)⁻¹ *
      ⟨1, 0, x.γ, 0⟩ * ⟨1, 1, 0, 0⟩ := by
    rw [commutator_P]
    ext <;> simp [hx.1, hx.2.1, hx.2.2]
  rw [e]
  have h1 := Subgroup.commutator_mem_commutator (H₁ := P σ) (H₂ := P σ)
    (g₁ := (⟨1, 0, x.γ, 0⟩ : ThompsonN K σ)⁻¹) (g₂ := (⟨1, 1, 0, 0⟩ : ThompsonN K σ)⁻¹)
    (P σ |>.inv_mem rfl) (P σ |>.inv_mem rfl)
  rwa [commutatorElement_def, inv_inv, inv_inv] at h1

theorem commutator_commutator_P_le : ⁅⁅P σ, P σ⁆, P σ⁆ ≤ Zc σ := by
  refine (Subgroup.commutator_mono (commutator_P_le (σ := σ)) le_rfl).trans ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  have hx2 := (P2 σ).inv_mem hx
  have hx' : x⁻¹ = ⟨1, 0, x⁻¹.β, x⁻¹.γ⟩ := by ext <;> simp [hx2.1, hx2.2]
  have hy' := eq_of_mem_P (P σ |>.inv_mem hy)
  have e : x * y * x⁻¹ * y⁻¹ = x⁻¹⁻¹ * y⁻¹⁻¹ * x⁻¹ * y⁻¹ := by simp
  rw [e, hx', hy', commutator_P]
  exact ⟨rfl, rfl, by simp⟩

theorem mem_center_P (hσ : ∃ ξ : K, σ ξ ≠ ξ) {x : ThompsonN K σ} :
    x ∈ (Subgroup.center (P σ)).map (P σ).subtype ↔ x ∈ Zc σ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hx := eq_of_mem_P w.2
    have hc : ∀ y ∈ P σ, (w : ThompsonN K σ)⁻¹ * y⁻¹ * w * y = 1 := fun y hy =>
      inv_mul_inv_mul_mul_eq_one_iff.2
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩)).symm
    have h1 := hc ⟨1, 1, 0, 0⟩ rfl
    rw [hx, commutator_P] at h1
    have hb1 : σ w.1.α - w.1.α = 0 := by
      have := congrArg ThompsonN.β h1; simpa using this
    obtain ⟨ξ₀, hξ₀⟩ := hσ
    have h2 := hc ⟨1, ξ₀, 0, 0⟩ rfl
    rw [hx, commutator_P] at h2
    have hb2 : σ w.1.α * ξ₀ - w.1.α * σ ξ₀ = 0 := by
      have := congrArg ThompsonN.β h2; simpa using this
    have hα : w.1.α = 0 := by
      have e : w.1.α * (ξ₀ - σ ξ₀) = 0 := by
        rw [sub_eq_zero.1 hb1] at hb2; linear_combination hb2
      exact (mul_eq_zero.1 e).resolve_right (sub_ne_zero.2 (Ne.symm hξ₀))
    have hβ : w.1.β = 0 := by
      have := congrArg ThompsonN.γ h1
      simp [hα] at this
      exact this
    exact ⟨mem_P.1 w.2, hα, hβ⟩
  · intro hx
    refine ⟨⟨x, hx.1⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
    have hx' : x = ⟨1, 0, 0, x.γ⟩ := by ext <;> simp [hx.1, hx.2.1, hx.2.2]
    have hy' := eq_of_mem_P y.2
    show y.1 * x = x * y.1
    rw [hx', hy', mul_P, mul_P]
    ext <;> simp; ring

variable (σ) in
@[expose] def J : ThompsonN K σ := torus σ (-1)

theorem J_conj (α β γ : K) :
    (J σ)⁻¹ * ⟨1, α, β, γ⟩ * J σ = ⟨1, -α, β, -γ⟩ := by
  rw [J, torus_conj]
  ext <;> simp

theorem mem_centralizer_J {x : ThompsonN K σ} (hx : x ∈ P σ) :
    x ∈ Subgroup.centralizer {J σ} ↔ x.α = 0 ∧ x.γ = 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h; have h3 := three_eq_zero (K := K)
    exact one_ne_zero (by linear_combination h3 - h)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hx' := eq_of_mem_P hx
  constructor
  · intro hc
    have e : (J σ)⁻¹ * x * J σ = x := by rw [mul_assoc, hc]; group
    rw [hx', J_conj] at e
    have ha := congrArg ThompsonN.α e
    have hg := congrArg ThompsonN.γ e
    simp only at ha hg
    refine ⟨?_, ?_⟩
    · have : 2 * x.α = 0 := by linear_combination -ha
      exact (mul_eq_zero.1 this).resolve_left h2
    · have : 2 * x.γ = 0 := by linear_combination -hg
      exact (mul_eq_zero.1 this).resolve_left h2
  · rintro ⟨ha, hg⟩
    have e : (J σ)⁻¹ * x * J σ = x := by
      rw [hx', J_conj, ha, hg, neg_zero]
    calc x * J σ = J σ * ((J σ)⁻¹ * x * J σ) := by group
      _ = J σ * x := by rw [e]

end ThompsonN

end CFSG.Walter.Ree
