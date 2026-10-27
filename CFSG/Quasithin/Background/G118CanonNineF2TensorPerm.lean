module

public import CFSG.Quasithin.Background.G118CanonNineF2Gap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Tensor

open scoped TensorProduct

theorem permAct_mul' {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    permAct (σ * τ) x = permAct σ (permAct τ x) := by
  funext i
  simp [permAct, mul_inv_rev, Equiv.Perm.mul_apply]

theorem permAct_one' {n : ℕ} (x : Fin n → ZMod 2) : permAct (1 : Equiv.Perm (Fin n)) x = x := by
  funext i
  simp [permAct]

theorem permActCore_one (n : ℕ) (x : ↥(permCore n)) : permActCore n 1 x = x :=
  Subtype.ext (permAct_one' _)

theorem permActCore_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (x : ↥(permCore n)) :
    permActCore n (σ * τ) x = permActCore n σ (permActCore n τ x) :=
  Subtype.ext (permAct_mul' _ _ _)

theorem permActCore_add (n : ℕ) (σ : Equiv.Perm (Fin n)) (x y : ↥(permCore n)) :
    permActCore n σ (x + y) = permActCore n σ x + permActCore n σ y :=
  Subtype.ext (funext fun _ => rfl)

theorem permActCore_smul (n : ℕ) (σ : Equiv.Perm (Fin n)) (a : ZMod 2) (x : ↥(permCore n)) :
    permActCore n σ (a • x) = a • permActCore n σ x :=
  Subtype.ext (funext fun _ => rfl)

@[expose] noncomputable def permActLin (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ↥(permCore n) ≃ₗ[ZMod 2] ↥(permCore n) where
  toFun := permActCore n σ
  invFun := permActCore n σ⁻¹
  map_add' := permActCore_add n σ
  map_smul' := fun a x => permActCore_smul n σ a x
  left_inv := fun x => by
    rw [← permActCore_mul, inv_mul_cancel, permActCore_one]
  right_inv := fun x => by
    rw [← permActCore_mul, mul_inv_cancel, permActCore_one]

theorem permActLin_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : ↥(permCore n)) :
    permActLin n σ x = permActCore n σ x := rfl

@[expose] def rho3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def tau3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

@[expose] def w1 : ↥(permCore 3) :=
  ⟨![1, 1, 0], by show ∑ i, (![1, 1, 0] : Fin 3 → ZMod 2) i = 0; decide⟩

@[expose] def w2 : ↥(permCore 3) :=
  ⟨![0, 1, 1], by show ∑ i, (![0, 1, 1] : Fin 3 → ZMod 2) i = 0; decide⟩

theorem rho3_pow_three : rho3 ^ 3 = 1 := by decide

theorem rho3_ne_one : rho3 ≠ 1 := by decide

theorem tau3_mul_self : tau3 * tau3 = 1 := by decide

theorem tau3_rho3 : tau3 * rho3 = rho3⁻¹ * tau3 := by decide

theorem perm3_cases (π : Equiv.Perm (Fin 3)) :
    π = 1 ∨ π = rho3 ∨ π = rho3 * rho3 ∨ π = tau3 ∨ π = tau3 * rho3 ∨ π = tau3 * rho3 * rho3 := by
  revert π
  decide

theorem rho3_w1 : permActCore 3 rho3 w1 = w2 := by
  apply Subtype.ext
  decide

theorem rho3_w2 : permActCore 3 rho3 w2 = w1 + w2 := by
  apply Subtype.ext
  decide

theorem tau3_w1 : permActCore 3 tau3 w1 = w1 := by
  apply Subtype.ext
  decide

theorem tau3_w2 : permActCore 3 tau3 w2 = w1 + w2 := by
  apply Subtype.ext
  decide

theorem decomp3 (x : ↥(permCore 3)) :
    x = (x : Fin 3 → ZMod 2) 0 • w1 + (x : Fin 3 → ZMod 2) 2 • w2 := by
  have hx : ∑ i, (x : Fin 3 → ZMod 2) i = 0 := x.2
  rw [Fin.sum_univ_three] at hx
  apply Subtype.ext
  funext i
  have key : ∀ a b c : ZMod 2, a + b + c = 0 → b = a + c := by decide
  fin_cases i
  · show (x : Fin 3 → ZMod 2) 0 = (x : Fin 3 → ZMod 2) 0 * 1 + (x : Fin 3 → ZMod 2) 2 * 0
    ring
  · show (x : Fin 3 → ZMod 2) 1 = (x : Fin 3 → ZMod 2) 0 * 1 + (x : Fin 3 → ZMod 2) 2 * 1
    rw [mul_one, mul_one]
    exact key _ _ _ hx
  · show (x : Fin 3 → ZMod 2) 2 = (x : Fin 3 → ZMod 2) 0 * 0 + (x : Fin 3 → ZMod 2) 2 * 1
    ring

@[expose] def coord0 : ↥(permCore 3) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 0).comp (permCore 3).subtype

@[expose] def coord2 : ↥(permCore 3) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 2).comp (permCore 3).subtype

theorem coord0_w1 : coord0 w1 = 1 := rfl

theorem coord0_w2 : coord0 w2 = 0 := rfl

theorem coord2_w1 : coord2 w1 = 0 := rfl

theorem coord2_w2 : coord2 w2 = 1 := rfl

theorem decomp3' (x : ↥(permCore 3)) : x = coord0 x • w1 + coord2 x • w2 :=
  decomp3 x

theorem tensor_decomp (t : ↥(permCore 3) ⊗[ZMod 2] ↥(permCore 5)) :
    ∃ a₁ a₂ : ↥(permCore 5), t = w1 ⊗ₜ a₁ + w2 ⊗ₜ a₂ := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x a =>
    refine ⟨coord0 x • a, coord2 x • a, ?_⟩
    conv_lhs => rw [decomp3' x]
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a₁, a₂, rfl⟩ := hx
    obtain ⟨a₁', a₂', rfl⟩ := hy
    exact ⟨a₁ + a₁', a₂ + a₂', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩

end F2Tensor

end Canon

end G11

end CFSG.Quasithin
