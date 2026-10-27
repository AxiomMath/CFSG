module

public import CFSG.Monster.Spin.Defs

public noncomputable section

namespace CFSG.Monster.Lifts

open CFSG.Monster.Code CFSG.Monster.Spin Matrix

theorem shift_eq_add_π₀ (a : C) (c : C₀) : shift a c = c + π₀ a := by
  rw [shift, map_add, π₀_coe]

theorem coe_shift_eq_add_π₀ (a : C) (c : C₀) :
    (shift a c : C) = (c : C) + (π₀ a : C) := by
  rw [shift_eq_add_π₀, Submodule.coe_add]

@[expose] def yPerm (a : C) (i : SpinIdx) : SpinIdx := if i.1 = 0 then (0, shift a i.2) else i

@[expose] def ySign (e : Parker) (i : SpinIdx) : ZMod 2 :=
  if i.1 = 0 then e.sign + θ i.2 e.code else K e.code ((i.2 : C) : Fin 24 → ZMod 2)

@[expose] def Ymat (e : Parker) : Matrix SpinIdx SpinIdx ℚ := spm ℚ (yPerm e.code) (ySign e)

theorem yPerm_zero (a : C) (c : C₀) : yPerm a (0, c) = (0, shift a c) := by
  simp [yPerm]

theorem yPerm_one (a : C) (c : C₀) : yPerm a (1, c) = (1, c) := by
  simp [yPerm]

theorem ySign_zero (e : Parker) (c : C₀) : ySign e (0, c) = e.sign + θ c e.code := by
  simp [ySign]

theorem ySign_one (e : Parker) (c : C₀) :
    ySign e (1, c) = K e.code ((c : C) : Fin 24 → ZMod 2) := by
  simp [ySign]

theorem yPerm_involutive (a : C) : Function.Involutive (yPerm a) := by
  rintro ⟨η, c⟩
  by_cases h : η = 0
  · subst h
    rw [yPerm_zero, yPerm_zero, shift_shift]
  · simp [yPerm, h]

theorem yPerm_bijective (a : C) : Function.Bijective (yPerm a) :=
  (yPerm_involutive a).bijective

theorem E_zero_vecMul_Ymat (e : Parker) (c : C₀) :
    E 0 c ᵥ* Ymat e = sgn (e.sign + θ c e.code) • E 0 (shift e.code c) := by
  rw [E, Ymat, single_vecMul_spm, yPerm_zero, ySign_zero, sgnR_rat]
  rfl

theorem E_one_vecMul_Ymat (e : Parker) (c : C₀) :
    E 1 c ᵥ* Ymat e = sgn (K e.code ((c : C) : Fin 24 → ZMod 2)) • E 1 c := by
  rw [E, Ymat, single_vecMul_spm, yPerm_one, ySign_one, sgnR_rat]

theorem Ymat_apply (e : Parker) (i j : SpinIdx) :
    Ymat e i j = if j = yPerm e.code i then sgn (ySign e i) else 0 := rfl

theorem Ymat_transpose_mul_self (e : Parker) : (Ymat e)ᵀ * Ymat e = 1 :=
  spm_transpose_mul_self (yPerm_involutive _) _

theorem Ymat_mul_transpose_self (e : Parker) : Ymat e * (Ymat e)ᵀ = 1 :=
  spm_mul_transpose_self (yPerm_involutive _) _

theorem Ymat_apply_mem (e : Parker) (i j : SpinIdx) :
    Ymat e i j = 0 ∨ Ymat e i j = 1 ∨ Ymat e i j = -1 :=
  spm_apply_mem _ _ _ _

@[expose] def YU (e : Parker) : GL SpinIdx ℚ :=
  ⟨Ymat e, (Ymat e)ᵀ, Ymat_mul_transpose_self e, Ymat_transpose_mul_self e⟩

@[simp] theorem coe_YU (e : Parker) : (YU e : Matrix SpinIdx SpinIdx ℚ) = Ymat e := rfl

@[expose] def gmat (a : C) : Matrix (Fin 24) (Fin 24) ℚ :=
  diagonal fun i => sgn ((a : Fin 24 → ZMod 2) i)

theorem gmat_eq_spm (a : C) :
    gmat a = spm ℚ (fun i => i) (fun i => (a : Fin 24 → ZMod 2) i) := by
  ext i j
  rw [gmat, diagonal_apply, spm_apply, sgnR_rat]
  by_cases h : i = j
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem single_vecMul_gmat (a : C) (i : Fin 24) :
    Pi.single i 1 ᵥ* gmat a = sgn ((a : Fin 24 → ZMod 2) i) • Pi.single i 1 := by
  rw [gmat_eq_spm, single_vecMul_spm, sgnR_rat]

theorem gmat_transpose (a : C) : (gmat a)ᵀ = gmat a := diagonal_transpose _

theorem gmat_mul_self (a : C) : gmat a * gmat a = 1 := by
  rw [gmat, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => sgnR_mul_self (R := ℚ) _)

theorem gmat_transpose_mul_self (a : C) : (gmat a)ᵀ * gmat a = 1 := by
  rw [gmat_transpose, gmat_mul_self]

theorem gmat_mul_transpose_self (a : C) : gmat a * (gmat a)ᵀ = 1 := by
  rw [gmat_transpose, gmat_mul_self]

theorem gmat_apply_mem (a : C) (i j : Fin 24) :
    gmat a i j = 0 ∨ gmat a i j = 1 ∨ gmat a i j = -1 := by
  rw [gmat_eq_spm]
  exact spm_apply_mem _ _ _ _

@[expose] def gU (a : C) : GL (Fin 24) ℚ := ⟨gmat a, gmat a, gmat_mul_self a, gmat_mul_self a⟩

@[simp] theorem coe_gU (a : C) : (gU a : Matrix (Fin 24) (Fin 24) ℚ) = gmat a := rfl

theorem code_sign_spin_lift_data :
    (∀ a : C, (π₀ a : C) = a + μ₀ a • ΩC ∧ ∀ c : C₀, shift a c = c + π₀ a) ∧
    (∀ (e : Parker) (c : C₀),
      E 1 c ᵥ* Ymat e = sgn (K e.code ((c : C) : Fin 24 → ZMod 2)) • E 1 c ∧
      E 0 c ᵥ* Ymat e = sgn (e.sign + θ c e.code) • E 0 (c + π₀ e.code)) ∧
    (∀ e : Parker, Ymat e = spm ℚ (yPerm e.code) (ySign e) ∧ Function.Bijective (yPerm e.code) ∧
      Function.Involutive (yPerm e.code)) ∧
    (∀ e : Parker, (Ymat e)ᵀ * Ymat e = 1 ∧ Ymat e * (Ymat e)ᵀ = 1) ∧
    (∀ (e : Parker) (i j : SpinIdx), Ymat e i j = 0 ∨ Ymat e i j = 1 ∨ Ymat e i j = -1) ∧
    (∀ a : C, gmat a = diagonal (fun i => sgn ((a : Fin 24 → ZMod 2) i)) ∧
      gmat a = spm ℚ (fun i => i) (fun i => (a : Fin 24 → ZMod 2) i)) ∧
    (∀ (a : C) (i : Fin 24),
      Pi.single i 1 ᵥ* gmat a = sgn ((a : Fin 24 → ZMod 2) i) • Pi.single i 1) ∧
    (∀ a : C, (gmat a)ᵀ * gmat a = 1 ∧ gmat a * (gmat a)ᵀ = 1) ∧
    (∀ (a : C) (i j : Fin 24), gmat a i j = 0 ∨ gmat a i j = 1 ∨ gmat a i j = -1) :=
  ⟨fun a => ⟨coe_π₀ a, shift_eq_add_π₀ a⟩,
    fun e c => ⟨E_one_vecMul_Ymat e c, by rw [E_zero_vecMul_Ymat, shift_eq_add_π₀]⟩,
    fun e => ⟨rfl, yPerm_bijective _, yPerm_involutive _⟩,
    fun e => ⟨Ymat_transpose_mul_self e, Ymat_mul_transpose_self e⟩, Ymat_apply_mem,
    fun a => ⟨rfl, gmat_eq_spm a⟩, single_vecMul_gmat,
    fun a => ⟨gmat_transpose_mul_self a, gmat_mul_transpose_self a⟩, gmat_apply_mem⟩

end CFSG.Monster.Lifts
