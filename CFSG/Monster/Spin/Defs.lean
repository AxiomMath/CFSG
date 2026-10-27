module

public import CFSG.Monster.Spin.Pairing
public import CFSG.Monster.Spin.SignedPerm
public import CFSG.Monster.Lagrangian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public noncomputable section

namespace CFSG.Monster.Spin

open CFSG.Monster.Code Matrix

abbrev SpinIdx : Type := ZMod 2 × C₀

theorem card_spinIdx : Fintype.card SpinIdx = 4096 := by
  rw [Fintype.card_eq_nat_card, Nat.card_prod, Nat.card_zmod, natCard_C₀]
  rfl

@[expose] def E (η : ZMod 2) (c : C₀) : SpinIdx → ℚ := Pi.single (η, c) 1

theorem E_dotProduct_E (η η' : ZMod 2) (c c' : C₀) :
    E η c ⬝ᵥ E η' c' = if (η, c) = (η', c') then 1 else 0 := by
  rw [E, E, single_dotProduct, one_mul, Pi.single_apply]

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

@[expose] def shift (a : C) (c : C₀) : C₀ := π₀ ((c : C) + a)

theorem coe_shift (a : C) (c : C₀) : (shift a c : C) = c + a + μ₀ a • ΩC := by
  rw [shift, coe_π₀, map_add, μ₀_coe, zero_add]

theorem shift_add (a b : C) (c : C₀) : shift (a + b) c = shift b (shift a c) := by
  simp only [shift, map_add, π₀_coe, add_assoc]

@[simp] theorem shift_zero (c : C₀) : shift 0 c = c := by
  simp only [shift, add_zero, π₀_coe]

theorem add_self_C' (a : C) : a + a = 0 := add_self_C a

theorem shift_shift (a : C) (c : C₀) : shift a (shift a c) = c := by
  rw [← shift_add, add_self_C', shift_zero]

theorem shift_ΩC (c : C₀) : shift ΩC c = c := by
  simp only [shift, map_add, π₀_coe, π₀_ΩC, add_zero]

theorem shift_eq_self_iff (a : C) (c : C₀) : shift a c = c ↔ π₀ a = 0 := by
  rw [shift, map_add, π₀_coe, add_eq_left]

theorem shift_injective (a : C) : Function.Injective (shift a) := by
  intro c c' h
  rw [← shift_shift a c, h, shift_shift]

theorem shift_surjective (a : C) : Function.Surjective (shift a) :=
  fun c => ⟨shift a c, shift_shift a c⟩

theorem pair_shift (a : C) (c : C₀) (δ : Cocode) :
    pair (shift a c) δ = pair c δ + pair a δ + μ₀ a * pair ΩC δ := by
  rw [coe_shift, pair_add_left, pair_add_left, pair_smul_left]

theorem θ_shift (b a : C) (c : C₀) : θ b (shift a c) = θ b c + θ b a := by
  rw [coe_shift, θ_add_right, θ_add_right, θ_smul_right, θ_ΩC_right, mul_zero, add_zero]

variable (R : Type*) [CommRing R]

@[expose] def xPerm (a : C) (i : SpinIdx) : SpinIdx := (i.1, shift a i.2)

@[expose] def xSign (e : Parker) (i : SpinIdx) : ZMod 2 :=
  e.sign + P e.code + θ e.code i.2 + i.1 * μ₀ e.code

@[expose] def dPerm (δ : Cocode) (i : SpinIdx) : SpinIdx := (i.1 + pair ΩC δ, i.2)

@[expose] def dSign (δ : Cocode) (i : SpinIdx) : ZMod 2 := pair i.2 δ

@[expose] def XmatR (e : Parker) : Matrix SpinIdx SpinIdx R := spm R (xPerm e.code) (xSign e)

@[expose] def DmatR (δ : Cocode) : Matrix SpinIdx SpinIdx R := spm R (dPerm δ) (dSign δ)

@[expose] def TmatR (a : C) : Matrix SpinIdx SpinIdx R :=
  XmatR R ⟨a, 0⟩ * DmatR R (thetaD a)

theorem xPerm_involutive (a : C) : Function.Involutive (xPerm a) := fun i => by
  simp only [xPerm, shift_shift]

theorem dPerm_involutive (δ : Cocode) : Function.Involutive (dPerm δ) := fun i => by
  simp only [dPerm, add_assoc, ← two_mul, two_eq_zero', zero_mul, add_zero]

variable {R}

theorem XmatR_transpose_mul_self (e : Parker) : (XmatR R e)ᵀ * XmatR R e = 1 :=
  spm_transpose_mul_self (xPerm_involutive _) _

theorem XmatR_mul_transpose_self (e : Parker) : XmatR R e * (XmatR R e)ᵀ = 1 :=
  spm_mul_transpose_self (xPerm_involutive _) _

theorem DmatR_transpose_mul_self (δ : Cocode) : (DmatR R δ)ᵀ * DmatR R δ = 1 :=
  spm_transpose_mul_self (dPerm_involutive _) _

theorem DmatR_mul_transpose_self (δ : Cocode) : DmatR R δ * (DmatR R δ)ᵀ = 1 :=
  spm_mul_transpose_self (dPerm_involutive _) _

theorem map_XmatR (e : Parker) : (XmatR ℤ e).map (Int.cast : ℤ → R) = XmatR R e :=
  map_spm (Int.castRingHom R) _ _

theorem map_DmatR (δ : Cocode) : (DmatR ℤ δ).map (Int.cast : ℤ → R) = DmatR R δ :=
  map_spm (Int.castRingHom R) _ _

theorem map_TmatR (a : C) : (TmatR ℤ a).map (Int.cast : ℤ → R) = TmatR R a := by
  have h := Matrix.map_mul (L := XmatR ℤ ⟨a, 0⟩) (M := DmatR ℤ (thetaD a))
    (f := Int.castRingHom R)
  rw [Int.coe_castRingHom] at h
  rw [TmatR, TmatR, h, map_XmatR, map_DmatR]

@[expose] def Xmat (e : Parker) : Matrix SpinIdx SpinIdx ℚ := XmatR ℚ e

@[expose] def Dmat (δ : Cocode) : Matrix SpinIdx SpinIdx ℚ := DmatR ℚ δ

@[expose] def zmat : Matrix SpinIdx SpinIdx ℚ := -1

@[expose] def Tmat (a : C) : Matrix SpinIdx SpinIdx ℚ := Xmat ⟨a, 0⟩ * Dmat (thetaD a)

theorem Xmat_eq (e : Parker) : Xmat e = XmatR ℚ e := rfl

theorem Dmat_eq (δ : Cocode) : Dmat δ = DmatR ℚ δ := rfl

theorem Tmat_eq (a : C) : Tmat a = TmatR ℚ a := rfl

theorem sgnR_rat : sgnR ℚ = sgn := rfl

theorem E_vecMul_Xmat (e : Parker) (η : ZMod 2) (c : C₀) :
    E η c ᵥ* Xmat e = sgn (e.sign + P e.code + θ e.code c + η * μ₀ e.code) •
      E η (shift e.code c) :=
  single_vecMul_spm _ _ _

theorem E_vecMul_Dmat (δ : Cocode) (η : ZMod 2) (c : C₀) :
    E η c ᵥ* Dmat δ = sgn (pair c δ) • E (η + pair ΩC δ) c :=
  single_vecMul_spm _ _ _

theorem Xmat_apply (e : Parker) (i j : SpinIdx) :
    Xmat e i j = if j = (i.1, shift e.code i.2) then
      sgn (e.sign + P e.code + θ e.code i.2 + i.1 * μ₀ e.code) else 0 := rfl

theorem Dmat_apply (δ : Cocode) (i j : SpinIdx) :
    Dmat δ i j = if j = (i.1 + pair ΩC δ, i.2) then sgn (pair i.2 δ) else 0 := rfl

theorem Xmat_transpose_mul_self (e : Parker) : (Xmat e)ᵀ * Xmat e = 1 :=
  XmatR_transpose_mul_self e

theorem Xmat_mul_transpose_self (e : Parker) : Xmat e * (Xmat e)ᵀ = 1 :=
  XmatR_mul_transpose_self e

theorem Dmat_transpose_mul_self (δ : Cocode) : (Dmat δ)ᵀ * Dmat δ = 1 :=
  DmatR_transpose_mul_self δ

theorem Dmat_mul_transpose_self (δ : Cocode) : Dmat δ * (Dmat δ)ᵀ = 1 :=
  DmatR_mul_transpose_self δ

theorem Xmat_apply_mem (e : Parker) (i j : SpinIdx) :
    Xmat e i j = 0 ∨ Xmat e i j = 1 ∨ Xmat e i j = -1 :=
  spm_apply_mem _ _ _ _

theorem Dmat_apply_mem (δ : Cocode) (i j : SpinIdx) :
    Dmat δ i j = 0 ∨ Dmat δ i j = 1 ∨ Dmat δ i j = -1 :=
  spm_apply_mem _ _ _ _

theorem Xmat_eq_map (e : Parker) : Xmat e = (XmatR ℤ e).map (Int.cast : ℤ → ℚ) :=
  (map_XmatR e).symm

theorem Dmat_eq_map (δ : Cocode) : Dmat δ = (DmatR ℤ δ).map (Int.cast : ℤ → ℚ) :=
  (map_DmatR δ).symm

@[expose] def XU (e : Parker) : GL SpinIdx ℚ :=
  ⟨Xmat e, (Xmat e)ᵀ, Xmat_mul_transpose_self e, Xmat_transpose_mul_self e⟩

@[expose] def DU (δ : Cocode) : GL SpinIdx ℚ :=
  ⟨Dmat δ, (Dmat δ)ᵀ, Dmat_mul_transpose_self δ, Dmat_transpose_mul_self δ⟩

@[simp] theorem coe_XU (e : Parker) : (XU e : Matrix SpinIdx SpinIdx ℚ) = Xmat e := rfl

@[simp] theorem coe_DU (δ : Cocode) : (DU δ : Matrix SpinIdx SpinIdx ℚ) = Dmat δ := rfl

@[expose] def Q : Subgroup (GL SpinIdx ℚ) := Subgroup.closure (Set.range XU ∪ Set.range DU)

theorem XU_mem_Q (e : Parker) : XU e ∈ Q :=
  Subgroup.subset_closure (Or.inl ⟨e, rfl⟩)

theorem DU_mem_Q (δ : Cocode) : DU δ ∈ Q :=
  Subgroup.subset_closure (Or.inr ⟨δ, rfl⟩)

theorem spin_signed_matrix_data :
    μ₀ ΩC = 1 ∧ Nat.card C₀ = 2 ^ 11 ∧ Fintype.card SpinIdx = 4096 ∧
    (∀ (a : C) (x : Fin 24 → ZMod 2), pair a (Submodule.Quotient.mk x) =
      (a : Fin 24 → ZMod 2) ⬝ᵥ x) ∧
    (∀ f : C →ₗ[ZMod 2] ZMod 2, ∃! δ : Cocode, ∀ u : C, pair u δ = f u) ∧
    (∀ a : C, (∀ u : C, pair u (thetaD a) = θ a u) ∧
      ∀ δ : Cocode, (∀ u : C, pair u δ = θ a u) → δ = thetaD a) ∧
    (∀ (e : Parker) (η : ZMod 2) (c : C₀), E η c ᵥ* Xmat e =
      sgn (e.sign + P e.code + θ e.code c + η * μ₀ e.code) • E η (shift e.code c) ∧
      (shift e.code c : C) = c + e.code + μ₀ e.code • ΩC) ∧
    (∀ (δ : Cocode) (η : ZMod 2) (c : C₀), E η c ᵥ* Dmat δ = sgn (pair c δ) • E (η + pair ΩC δ) c) ∧
    zmat = -1 ∧ (∀ a : C, Tmat a = Xmat ⟨a, 0⟩ * Dmat (thetaD a)) ∧
    (∀ e : Parker, (Xmat e)ᵀ * Xmat e = 1 ∧ Xmat e * (Xmat e)ᵀ = 1) ∧
    (∀ δ : Cocode, (Dmat δ)ᵀ * Dmat δ = 1 ∧ Dmat δ * (Dmat δ)ᵀ = 1) ∧
    (∀ (e : Parker) (i j : SpinIdx), Xmat e i j = 0 ∨ Xmat e i j = 1 ∨ Xmat e i j = -1) ∧
    (∀ (δ : Cocode) (i j : SpinIdx), Dmat δ i j = 0 ∨ Dmat δ i j = 1 ∨ Dmat δ i j = -1) ∧
    (∀ e : Parker, (XU e : Matrix SpinIdx SpinIdx ℚ) = Xmat e) ∧
    (∀ δ : Cocode, (DU δ : Matrix SpinIdx SpinIdx ℚ) = Dmat δ) ∧
    Q = Subgroup.closure (Set.range XU ∪ Set.range DU) :=
  ⟨μ₀_ΩC, natCard_C₀, card_spinIdx, pair_mk, pair_perfect,
    fun a => ⟨pair_thetaD a, fun _ h => thetaD_unique h⟩,
    fun e η c => ⟨E_vecMul_Xmat e η c, coe_shift e.code c⟩, E_vecMul_Dmat, rfl, fun _ => rfl,
    fun e => ⟨Xmat_transpose_mul_self e, Xmat_mul_transpose_self e⟩,
    fun δ => ⟨Dmat_transpose_mul_self δ, Dmat_mul_transpose_self δ⟩, Xmat_apply_mem,
    Dmat_apply_mem, coe_XU, coe_DU, rfl⟩

end CFSG.Monster.Spin
