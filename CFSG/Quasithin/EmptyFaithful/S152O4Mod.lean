module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin

namespace S152O4

@[expose] def Vec : Type := Fin 16

namespace Vec

@[expose] def mk (n : ℕ) : Vec := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

@[expose] def code (v : Vec) : ℕ := (v : Fin 16).val

instance : DecidableEq Vec := inferInstanceAs (DecidableEq (Fin 16))

instance : Fintype Vec := inferInstanceAs (Fintype (Fin 16))

instance : Mul Vec := ⟨fun a b => mk (code a ^^^ code b)⟩

instance : One Vec := ⟨mk 0⟩

instance : Inv Vec := ⟨fun a => a⟩

theorem mul_assoc' : ∀ a b c : Vec, a * b * c = a * (b * c) := by decide +kernel

theorem one_mul' : ∀ a : Vec, 1 * a = a := by decide +kernel

theorem mul_one' : ∀ a : Vec, a * 1 = a := by decide +kernel

theorem inv_mul_cancel' : ∀ a : Vec, a⁻¹ * a = 1 := by decide +kernel

theorem mul_comm' : ∀ a b : Vec, a * b = b * a := by decide +kernel

instance : CommGroup Vec where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'
  mul_comm := mul_comm'

theorem mul_self_eq_one (v : Vec) : v * v = 1 := by
  have := inv_mul_cancel' v
  exact this

end Vec

abbrev Gam : Type := DihedralGroup 3 × DihedralGroup 3

@[expose] def mulB (A B : ℕ) : ℕ :=
  (A % 2 * (B % 2) + A / 2 % 2 * (B / 4 % 2)) % 2 +
    2 * ((A % 2 * (B / 2 % 2) + A / 2 % 2 * (B / 8 % 2)) % 2) +
    4 * ((A / 4 % 2 * (B % 2) + A / 8 % 2 * (B / 4 % 2)) % 2) +
    8 * ((A / 4 % 2 * (B / 2 % 2) + A / 8 % 2 * (B / 8 % 2)) % 2)

@[expose] def matN : DihedralGroup 3 → ℕ
  | DihedralGroup.r i => if i = 0 then 9 else if i = 1 then 14 else 7
  | DihedralGroup.sr i => if i = 0 then 6 else if i = 1 then 11 else 13

@[expose] def actN (g : Gam) (n : ℕ) : ℕ := mulB (mulB (matN g.1) n) (matN g.2⁻¹)

@[expose] def act (g : Gam) (v : Vec) : Vec := Vec.mk (actN g (Vec.code v))

theorem act_mul : ∀ (g h : Gam) (v : Vec), act (g * h) v = act g (act h v) := by decide +kernel

theorem act_one : ∀ v : Vec, act 1 v = v := by decide +kernel

theorem act_mul_mul : ∀ (g : Gam) (v w : Vec), act g (v * w) = act g v * act g w := by
  decide +kernel

@[expose] def actAut (g : Gam) : MulAut Vec where
  toFun := act g
  invFun := act g⁻¹
  left_inv := fun v => by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv := fun v => by rw [← act_mul, mul_inv_cancel, act_one]
  map_mul' := act_mul_mul g

@[expose] def rho : Gam →* MulAut Vec where
  toFun := actAut
  map_one' := by
    ext v
    exact act_one v
  map_mul' := fun g h => by
    ext v
    exact act_mul g h v

theorem rho_apply (g : Gam) (v : Vec) : rho g v = act g v := rfl

theorem rho_ker : ∀ g : Gam, (∀ v : Vec, act g v = v) → g = 1 := by decide +kernel

theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact rho_ker g fun v => by
    have := congrArg (fun f : MulAut Vec => f v) hg
    simpa [rho_apply] using this

@[expose] def detN (n : ℕ) : ℕ := (n % 2 * (n / 8 % 2) + n / 2 % 2 * (n / 4 % 2)) % 2

@[expose] def detQ (v : Vec) : ZMod 2 := (detN (Vec.code v) : ZMod 2)

theorem detN_act : ∀ (g : Gam) (v : Vec), detN (Vec.code (act g v)) = detN (Vec.code v) := by
  decide +kernel

theorem detQ_act (g : Gam) (v : Vec) : detQ (act g v) = detQ v := by
  unfold detQ
  rw [detN_act]

theorem fixCount : ∀ g : Gam, Fintype.card {v : Vec // act g v = v} = 1 ∨
    Fintype.card {v : Vec // act g v = v} = 4 ∨ Fintype.card {v : Vec // act g v = v} = 16 := by
  decide +kernel

@[expose] def transN (n : ℕ) : ℕ := n % 2 + 2 * (n / 4 % 2) + 4 * (n / 2 % 2) + 8 * (n / 8 % 2)

@[expose] def transV : MulAut Vec where
  toFun v := Vec.mk (transN (Vec.code v))
  invFun v := Vec.mk (transN (Vec.code v))
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

theorem detQ_trans : ∀ v : Vec, detQ (transV v) = detQ v := by decide +kernel

theorem transCount : Fintype.card {v : Vec // transV v = v} = 8 := by decide +kernel

@[expose] def comm1 (b : Gam) (v : Vec) : Vec := act b v * v⁻¹

theorem pow_four_sq : ∀ γ : Gam, γ ^ 4 = 1 → γ ^ 2 = 1 := by decide +kernel

theorem pow_six : ∀ γ : Gam, γ ^ 6 = 1 := by decide +kernel

theorem conj_pow_three : ∀ γ ε : Gam, ε ^ 3 = 1 → (γ * ε * γ⁻¹) ^ 3 = 1 := by decide +kernel

theorem mul_pow_three : ∀ ε ε' : Gam, ε ^ 3 = 1 → ε' ^ 3 = 1 → (ε * ε') ^ 3 = 1 := by
  decide +kernel

theorem pow_three_comm : ∀ ε ε' : Gam, ε ^ 3 = 1 → ε' ^ 3 = 1 → ε * ε' = ε' * ε := by
  decide +kernel

theorem card_Gam : Nat.card Gam = 36 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_pow_three : Fintype.card {γ : Gam // γ ^ 3 = 1} = 9 := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem model_stab : ∀ β α : Gam, β ^ 2 = 1 → β ≠ 1 → α ^ 3 = 1 → α ≠ 1 →
    (∀ γ : Gam, γ ^ 3 = 1 → β * γ = γ * β → γ = 1) →
    ¬ (∀ γ : Gam, γ * α * γ⁻¹ = α ∨ γ * α * γ⁻¹ = α⁻¹) →
    ∃ z : Vec, z ≠ 1 ∧ (∃ v, z = comm1 β v) ∧
      (∀ γ : Gam, act γ z = z ↔ ∃ i : Fin 3, ∃ j : Fin 2, γ = α ^ (i : ℕ) * β ^ (j : ℕ)) ∧
      ∃ τ : Gam, τ * β = β * τ ∧ act τ z ≠ z := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem model_Z152_one : ∀ s s' b₀ : Gam, s ^ 2 = 1 → s' ^ 2 = 1 → s ≠ 1 → s' ≠ 1 → s ≠ s' →
    s * s' = s' * s → (b₀ = s ∨ b₀ = s' ∨ b₀ = s * s') →
    (∀ γ : Gam, γ ^ 3 = 1 → b₀ * γ * b₀⁻¹ = γ⁻¹) →
    ∃ t : Gam, (t = 1 ∨ t = s ∨ t = s' ∨ t = s * s') ∧
      ∃ v : Vec, act t (comm1 b₀ v) ≠ comm1 b₀ v := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem model_Z152_two : ∀ s s' : Gam, s ^ 2 = 1 → s' ^ 2 = 1 → s ≠ 1 → s' ≠ 1 → s ≠ s' →
    s * s' = s' * s →
    ∃ z₀ : Vec, act s z₀ = z₀ ∧ act s' z₀ = z₀ ∧
      ∀ α : Gam, α ^ 3 = 1 → act α z₀ = z₀ → α = 1 := by
  decide +kernel

end S152O4

end CFSG.Quasithin
