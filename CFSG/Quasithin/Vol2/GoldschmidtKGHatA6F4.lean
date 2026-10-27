module

public import CFSG.Fischer.F4
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Vol2.KGHat

open CFSG.Fischer

@[expose] def f4a (x : F4) : ZMod 2 := ((x.code.val % 2 : ℕ) : ZMod 2)

@[expose] def f4b (x : F4) : ZMod 2 := ((x.code.val / 2 : ℕ) : ZMod 2)

theorem f4a_add : ∀ x y : F4, f4a (x + y) = f4a x + f4a y := by decide +kernel

theorem f4b_add : ∀ x y : F4, f4b (x + y) = f4b x + f4b y := by decide +kernel

theorem f4a_mul : ∀ x y : F4, f4a (x * y) = f4a x * f4a y + f4b x * f4b y := by decide +kernel

theorem f4b_mul :
    ∀ x y : F4, f4b (x * y) = f4a x * f4b y + f4b x * f4a y + f4b x * f4b y := by decide +kernel

theorem f4a_one : f4a 1 = 1 := by decide +kernel

theorem f4b_one : f4b 1 = 0 := by decide +kernel

theorem f4a_zero : f4a 0 = 0 := by decide +kernel

theorem f4b_zero : f4b 0 = 0 := by decide +kernel

theorem f4a_omega : f4a F4.ω = 0 := by decide +kernel

theorem f4b_omega : f4b F4.ω = 1 := by decide +kernel

theorem omega_ne_zero : F4.ω ≠ 0 := fun h => by
  have := congrArg f4b h
  rw [f4b_omega, f4b_zero] at this
  exact absurd this (by decide)

theorem omega_ne_one : F4.ω ≠ 1 := fun h => by
  have := congrArg f4b h
  rw [f4b_omega, f4b_one] at this
  exact absurd this (by decide)

theorem omega_pow_eq_one {n : ℕ} (h : F4.ω ^ n = 1) : 3 ∣ n := by
  have h3 : F4.ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one F4.ω omega_ne_zero
    rwa [F4.card] at this
  have : orderOf F4.ω = 3 := orderOf_eq_prime h3 omega_ne_one
  rw [← this]
  exact orderOf_dvd_of_pow_eq_one h

section Module

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[reducible, expose] def f4Module (z : W →ₗ[ZMod 2] W) (hz : ∀ w, z (z w) = z w + w) :
    Module F4 W where
  smul x w := f4a x • w + f4b x • z w
  one_smul w := by
    show f4a 1 • w + f4b 1 • z w = w
    rw [f4a_one, f4b_one]
    simp
  mul_smul x y w := by
    have h1 : z (f4a y • w + f4b y • z w) = f4a y • z w + f4b y • (z w + w) := by
      rw [map_add, map_smul, map_smul, hz]
    show f4a (x * y) • w + f4b (x * y) • z w =
      f4a x • (f4a y • w + f4b y • z w) + f4b x • z (f4a y • w + f4b y • z w)
    rw [h1, f4a_mul, f4b_mul]
    module
  smul_zero x := by
    show f4a x • (0 : W) + f4b x • z 0 = 0
    simp
  smul_add x w w' := by
    show f4a x • (w + w') + f4b x • z (w + w') =
      (f4a x • w + f4b x • z w) + (f4a x • w' + f4b x • z w')
    rw [map_add]
    module
  add_smul x y w := by
    show f4a (x + y) • w + f4b (x + y) • z w =
      (f4a x • w + f4b x • z w) + (f4a y • w + f4b y • z w)
    rw [f4a_add, f4b_add]
    module
  zero_smul w := by
    show f4a 0 • w + f4b 0 • z w = 0
    rw [f4a_zero, f4b_zero]
    simp

@[expose] def F4Space (_z : W →ₗ[ZMod 2] W) (_hz : ∀ w, _z (_z w) = _z w + w) : Type _ := W

variable (z : W →ₗ[ZMod 2] W) (hz : ∀ w, z (z w) = z w + w)

instance : AddCommGroup (F4Space z hz) := inferInstanceAs (AddCommGroup W)

instance : Module (ZMod 2) (F4Space z hz) := inferInstanceAs (Module (ZMod 2) W)

instance : Module F4 (F4Space z hz) := f4Module z hz

instance [Finite W] : Finite (F4Space z hz) := inferInstanceAs (Finite W)

@[expose] def F4Space.val (w : F4Space z hz) : W := w

@[expose] def F4Space.mk (w : W) : F4Space z hz := w

theorem F4Space.smul_val (x : F4) (w : F4Space z hz) :
    (x • w).val = f4a x • w.val + f4b x • z w.val := rfl

theorem F4Space.omega_smul_val (w : F4Space z hz) : (F4.ω • w).val = z w.val := by
  rw [F4Space.smul_val, f4a_omega, f4b_omega]
  simp

@[expose] def toF4Lin (g : W →ₗ[ZMod 2] W) (hg : ∀ x, g (z x) = z (g x)) :
    F4Space z hz →ₗ[F4] F4Space z hz where
  toFun w := F4Space.mk z hz (g w.val)
  map_add' a b := by
    show g (a.val + b.val) = g a.val + g b.val
    exact map_add g _ _
  map_smul' x w := by
    show g (f4a x • w.val + f4b x • z w.val) = f4a x • g w.val + f4b x • z (g w.val)
    rw [map_add, map_smul, map_smul, hg]

theorem toF4Lin_val (g : W →ₗ[ZMod 2] W) (hg : ∀ x, g (z x) = z (g x)) (w : F4Space z hz) :
    (toF4Lin z hz g hg w).val = g w.val := rfl

theorem natCard_F4Space [Finite W] :
    Nat.card (F4Space z hz) = 4 ^ Module.finrank F4 (F4Space z hz) := by
  have : Module.Finite F4 (F4Space z hz) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := F4)]
  congr 1
  rw [Nat.card_eq_fintype_card, F4.card]

section Det

variable {Γ : Type*} [Group Γ]

@[expose] def f4Action (α : Γ →* (W →ₗ[ZMod 2] W)) (hα : ∀ γ x, α γ (z x) = z (α γ x)) :
    Γ →* (F4Space z hz →ₗ[F4] F4Space z hz) where
  toFun γ := toF4Lin z hz (α γ) (hα γ)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    show (α 1) x.val = x.val
    rw [map_one]
    rfl
  map_mul' γ δ := by
    refine LinearMap.ext fun x => ?_
    show (α (γ * δ)) x.val = (α γ) ((α δ) x.val)
    rw [map_mul]
    rfl

theorem f4Action_val (α : Γ →* (W →ₗ[ZMod 2] W)) (hα : ∀ γ x, α γ (z x) = z (α γ x)) (γ : Γ)
    (x : F4Space z hz) : (f4Action z hz α hα γ x).val = α γ x.val := rfl

theorem det_f4Action_eq_one (hΓ : Group.IsPerfect Γ) (α : Γ →* (W →ₗ[ZMod 2] W))
    (hα : ∀ γ x, α γ (z x) = z (α γ x)) (γ : Γ) :
    LinearMap.det (f4Action z hz α hα γ) = 1 := by
  let du : Γ →* F4ˣ := (LinearMap.det.comp (f4Action z hz α hα)).toHomUnits
  have hker : commutator Γ ≤ du.ker := Abelianization.commutator_subset_ker du
  have h1 : du γ = 1 := by
    have : γ ∈ du.ker := hker (by rw [hΓ.commutator_eq_top]; exact Subgroup.mem_top γ)
    exact this
  have h2 := congrArg Units.val h1
  simpa [du] using h2

theorem f4Action_eq_omega_smul (α : Γ →* (W →ₗ[ZMod 2] W))
    (hα : ∀ γ x, α γ (z x) = z (α γ x)) (z₀ : Γ) (hz₀ : ∀ x, α z₀ x = z x) :
    f4Action z hz α hα z₀ = F4.ω • (LinearMap.id : F4Space z hz →ₗ[F4] F4Space z hz) := by
  refine LinearMap.ext fun x => ?_
  show α z₀ x.val = (F4.ω • x).val
  rw [F4Space.omega_smul_val, hz₀]

theorem three_dvd_finrank (hΓ : Group.IsPerfect Γ) (α : Γ →* (W →ₗ[ZMod 2] W))
    (hα : ∀ γ x, α γ (z x) = z (α γ x)) (z₀ : Γ) (hz₀ : ∀ x, α z₀ x = z x) :
    3 ∣ Module.finrank F4 (F4Space z hz) := by
  have h1 := det_f4Action_eq_one z hz hΓ α hα z₀
  rw [f4Action_eq_omega_smul z hz α hα z₀ hz₀, LinearMap.det_smul, LinearMap.det_id,
    mul_one] at h1
  exact omega_pow_eq_one h1

end Det

end Module

end CFSG.Quasithin.Vol2.KGHat
