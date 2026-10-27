module

public import CFSG.Quasithin.Background.HL3WrWreath

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix
open scoped Matrix

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def c3m' : Mat3 := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

@[expose] def u0m : Mat3 := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[expose] def IsV5 (A : Mat3) : Prop := A 1 1 = 0 ∧ A 1 2 = 0 ∧ A 2 1 = 0 ∧ A 2 2 = 0

instance : DecidablePred IsV5 := fun A => by unfold IsV5; infer_instance

@[expose] def blk2 (A : Mat3) : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![A 1 1, A 1 2; A 2 1, A 2 2]

theorem mat_c3' : mat c3 = c3m' := rfl

theorem mat_u0 : mat u0 = u0m := rfl

theorem col_of_c3m : ∀ A : Mat3, IsV5 A → (A 1 0 ≠ 0 ∨ A 2 0 ≠ 0) →
    (Matrix.single 1 0 1 = c3m' * A + A ∨ Matrix.single 1 0 1 = c3m' * (c3m' * A + A) ∨
      Matrix.single 1 0 1 = (c3m' * A + A) + c3m' * (c3m' * A + A)) ∧
    (Matrix.single 2 0 1 = c3m' * A + A ∨ Matrix.single 2 0 1 = c3m' * (c3m' * A + A) ∨
      Matrix.single 2 0 1 = (c3m' * A + A) + c3m' * (c3m' * A + A)) := by
  decide +kernel

theorem row_of_c3m : ∀ A : Mat3, IsV5 A → (A 0 1 ≠ 0 ∨ A 0 2 ≠ 0) →
    (Matrix.single 0 1 1 = A * c3m'ᵀ + A ∨ Matrix.single 0 1 1 = (A * c3m'ᵀ + A) * c3m'ᵀ ∨
      Matrix.single 0 1 1 = (A * c3m'ᵀ + A) + (A * c3m'ᵀ + A) * c3m'ᵀ) ∧
    (Matrix.single 0 2 1 = A * c3m'ᵀ + A ∨ Matrix.single 0 2 1 = (A * c3m'ᵀ + A) * c3m'ᵀ ∨
      Matrix.single 0 2 1 = (A * c3m'ᵀ + A) + (A * c3m'ᵀ + A) * c3m'ᵀ) := by
  decide +kernel

theorem col_one_ne_zero : ∀ g : Mat3, g.det ≠ 0 → g 1 0 = 0 → g 2 0 = 0 →
    (g 1 1 ≠ 0 ∨ g 2 1 ≠ 0) := by
  decide +kernel

theorem rank_one_of_u0m : ∀ A : Mat3, blk2 A ≠ 0 → (blk2 A).det ≠ 0 →
    blk2 (u0m * A + A) ≠ 0 ∧ (blk2 (u0m * A + A)).det = 0 := by
  decide +kernel

theorem exists_c3_pow_blk : ∀ A : Mat3, blk2 A ≠ 0 → (blk2 A).det = 0 →
    ∃ i j : Fin 3, blk2 (c3m' ^ (i : ℕ) * A * (c3m' ^ (j : ℕ))ᵀ) = !![1, 0; 0, 0] := by
  decide +kernel

theorem single_c3m :
    Matrix.single 1 1 1 * c3m'ᵀ = (Matrix.single 1 2 1 : Mat3) ∧
      c3m' * Matrix.single 1 1 1 = (Matrix.single 2 1 1 : Mat3) ∧
      c3m' * Matrix.single 1 1 1 * c3m'ᵀ = (Matrix.single 2 2 1 : Mat3) := by
  decide +kernel

@[expose] def blkPart (A : Mat3) : Mat3 :=
  A 1 1 • Matrix.single 1 1 1 + A 1 2 • Matrix.single 1 2 1 + A 2 1 • Matrix.single 2 1 1 +
    A 2 2 • Matrix.single 2 2 1

theorem isV5_add_blkPart : ∀ A : Mat3, IsV5 (A + blkPart A) := by
  unfold blkPart
  decide +kernel

theorem eq_of_isV5 : ∀ A : Mat3, IsV5 A →
    A = A 0 0 • Matrix.single 0 0 1 + A 0 1 • Matrix.single 0 1 1 + A 0 2 • Matrix.single 0 2 1 +
      A 1 0 • Matrix.single 1 0 1 + A 2 0 • Matrix.single 2 0 1 := by
  decide +kernel

@[expose] def dd (i j k l : ℕ) (A : Mat3) : Mat3 :=
  c3m' ^ i * (c3m' ^ k * A * (c3m' ^ l)ᵀ + A) * (c3m' ^ j)ᵀ + (c3m' ^ k * A * (c3m' ^ l)ᵀ + A)

theorem e9_facts : ∀ i j k l : Fin 3, (i : ℕ) * l % 3 ≠ (j : ℕ) * k % 3 →
    ¬ ((∀ p q : Fin 3, IsV5 (dd i j k l (Matrix.single p q 1))) ∧
      ∀ p q : Fin 3, IsV5 (Matrix.single p q 1) →
        dd i j k l (Matrix.single p q 1) = 0 ∨
          dd i j k l (Matrix.single p q 1) = Matrix.single 0 0 1) := by
  unfold dd
  decide +kernel

theorem e9_moves : ∀ i j : Fin 3, ((i : ℕ), (j : ℕ)) ≠ (0, 0) →
    ∃ A : Mat3, ¬ IsV5 (c3m' ^ (i : ℕ) * A * (c3m' ^ (j : ℕ))ᵀ + A) := by
  decide +kernel

theorem eq_zero_or_of_isV5 : ∀ A : Mat3, IsV5 A → A 1 0 = 0 → A 2 0 = 0 → A 0 1 = 0 →
    A 0 2 = 0 → A = 0 ∨ A = Matrix.single 0 0 1 := by
  decide +kernel

theorem isV5_iff_blk2 : ∀ A : Mat3, IsV5 A ↔ blk2 A = 0 := by
  decide +kernel

theorem isV5_add_of_blk2 : ∀ A : Mat3, blk2 A = !![1, 0; 0, 0] →
    IsV5 (A + Matrix.single 1 1 1) := by
  decide +kernel

theorem neg_eq_self' : ∀ A : Mat3, -A = A := by
  decide +kernel

theorem dep_of_eq : ∀ i j k l : Fin 3, (i : ℕ) * l % 3 = (j : ℕ) * k % 3 →
    ((i : ℕ), (j : ℕ)) = (0, 0) ∨
      ∃ t : Fin 3, (k : ℕ) = (i : ℕ) * t % 3 ∧ (l : ℕ) = (j : ℕ) * t % 3 := by
  decide

theorem mul_single01_mul_transpose (a b : Mat3) (i j : Fin 3) :
    (a * (Matrix.single 0 1 1 : Mat3) * bᵀ) i j = a i 0 * b j 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

theorem mul_single10_mul_transpose (a b : Mat3) (i j : Fin 3) :
    (a * (Matrix.single 1 0 1 : Mat3) * bᵀ) i j = a i 1 * b j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

theorem isV5_mul_mul_transpose {a b A : Mat3} (ha1 : a 1 0 = 0) (ha2 : a 2 0 = 0)
    (hb1 : b 1 0 = 0) (hb2 : b 2 0 = 0) (hA : IsV5 A) : IsV5 (a * A * bᵀ) := by
  obtain ⟨h11, h12, h21, h22⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, ha1, ha2, hb1, hb2, h11, h12, h21, h22]

@[expose] def V5 : Subgroup WMod where
  carrier := {X | IsV5 (Multiplicative.toAdd X)}
  mul_mem' := by
    intro X Y hX hY
    obtain ⟨h1, h2, h3, h4⟩ := hX
    obtain ⟨k1, k2, k3, k4⟩ := hY
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [toAdd_mul, h1, h2, h3, h4, k1, k2, k3, k4]
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  inv_mem' := by
    intro X hX
    obtain ⟨h1, h2, h3, h4⟩ := hX
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [toAdd_inv, h1, h2, h3, h4]

theorem mem_V5 {X : WMod} : X ∈ V5 ↔ IsV5 (Multiplicative.toAdd X) := Iff.rfl

@[expose] noncomputable def Z00 : Subgroup WMod := Subgroup.zpowers (eW 0 0)

theorem eW00_mul_self : eW 0 0 * eW 0 0 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  decide

theorem eW00_ne_one : eW 0 0 ≠ 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_one] at h'
  exact absurd h' (by decide)

theorem orderOf_eW00 : orderOf (eW 0 0) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq, eW00_mul_self]) eW00_ne_one

theorem mem_Z00_iff {X : WMod} :
    X ∈ Z00 ↔ Multiplicative.toAdd X = 0 ∨ Multiplicative.toAdd X = Matrix.single 0 0 1 := by
  classical
  rw [Z00, mem_zpowers_iff_mem_range_orderOf, orderOf_eW00]
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp h
    have hn' : n < 2 := Finset.mem_range.mp hn
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · left
      rw [pow_zero, toAdd_one]
    · right
      rw [pow_one]
      rfl
  · rintro (h | h)
    · have : X = 1 := Multiplicative.toAdd.injective (h.trans toAdd_one.symm)
      exact Finset.mem_image.mpr ⟨0, by simp, by rw [pow_zero, this]⟩
    · have : X = eW 0 0 := Multiplicative.toAdd.injective h
      exact Finset.mem_image.mpr ⟨1, by simp, by rw [pow_one, this]⟩

theorem eW00_mem_V5 : eW 0 0 ∈ V5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem Z00_le_V5 : Z00 ≤ V5 := (Subgroup.zpowers_le).mpr eW00_mem_V5

theorem toAdd_eW (i j : Fin 3) : Multiplicative.toAdd (eW i j) = Matrix.single i j 1 := rfl

theorem rho_mem_V5 {a b : ↥SL32} (ha : a ∈ P1) (hb : b ∈ P1) {X : WMod} (hX : X ∈ V5) :
    rho (a, b) X ∈ V5 := by
  obtain ⟨a1, a2, -⟩ := (mulVec_e0_iff _).1 ha
  obtain ⟨b1, b2, -⟩ := (mulVec_e0_iff _).1 hb
  rw [mem_V5, toAdd_rho]
  exact isV5_mul_mul_transpose a1 a2 b1 b2 hX

theorem tau_mem_V5 {X : WMod} (hX : X ∈ V5) : tau X ∈ V5 := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  rw [mem_V5, toAdd_tau]
  exact ⟨by simpa using h1, by simpa using h3, by simpa using h2, by simpa using h4⟩

theorem map_mem_V5_of_mem_stabE {x : MulAut WMod} (hx : x ∈ stabE) {X : WMod} (hX : X ∈ V5) :
    x X ∈ V5 := by
  obtain ⟨w, rfl⟩ := hx
  rw [thetaW_apply, MulAut.mul_apply]
  rcases mz2_cases w.right with h | h
  · rw [h, map_one]
    exact rho_mem_V5 (w.left 1).2 (w.left tq).2 hX
  · rw [h, tauPow_tq]
    exact rho_mem_V5 (w.left 1).2 (w.left tq).2 (tau_mem_V5 hX)

theorem map_mem_Z00_of_mem_stabE {x : MulAut WMod} (hx : x ∈ stabE) {X : WMod} (hX : X ∈ Z00) :
    x X ∈ Z00 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hX
  rw [map_zpow, (mem_stabE_iff.1 hx).2]
  exact Subgroup.zpow_mem_zpowers _ _

theorem exists_eq_rho_mul_tau {x : MulAut WMod} (hx : x ∈ stabE) (hxi : x ∉ img) :
    ∃ a b : ↥SL32, a ∈ P1 ∧ b ∈ P1 ∧ x = rho (a, b) * tau := by
  obtain ⟨w, rfl⟩ := hx
  rcases mz2_cases w.right with h | h
  · exfalso
    apply hxi
    rw [thetaW_apply, h, map_one, mul_one]
    exact rho_mem_img _
  · exact ⟨_, _, (w.left 1).2, (w.left tq).2, by rw [thetaW_apply, h, tauPow_tq]⟩

theorem toAdd_rho_c3_one (X : WMod) :
    Multiplicative.toAdd (rho (c3, 1) X) = c3m' * Multiplicative.toAdd X := by
  rw [toAdd_rho]
  simp [mat_c3', mat_one]

theorem toAdd_rho_one_c3 (X : WMod) :
    Multiplicative.toAdd (rho (1, c3) X) = Multiplicative.toAdd X * c3m'ᵀ := by
  rw [toAdd_rho]
  simp [mat_c3', mat_one]

theorem toAdd_rho_u0_one (X : WMod) :
    Multiplicative.toAdd (rho (u0, 1) X) = u0m * Multiplicative.toAdd X := by
  rw [toAdd_rho]
  simp [mat_u0, mat_one]

theorem toAdd_rho_pow (i j : ℕ) (X : WMod) :
    Multiplicative.toAdd (rho (c3 ^ i, c3 ^ j) X) =
      c3m' ^ i * Multiplicative.toAdd X * (c3m' ^ j)ᵀ := by
  rw [toAdd_rho, mat_pow, mat_pow, mat_c3']

theorem ofAdd_smul_mem {W : Subgroup WMod} (a : ZMod 2) {p q : Fin 3} (h : eW p q ∈ W) :
    Multiplicative.ofAdd (a • (Matrix.single p q 1 : Mat3)) ∈ W := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a with rfl | rfl
  · rw [zero_smul, ofAdd_zero]
    exact W.one_mem
  · rw [one_smul]
    exact h

theorem col_mem {W : Subgroup WMod} (h1 : ∀ X ∈ W, rho (c3, 1) X ∈ W) {X : WMod} (hXW : X ∈ W)
    (hX5 : X ∈ V5)
    (hcol : Multiplicative.toAdd X 1 0 ≠ 0 ∨ Multiplicative.toAdd X 2 0 ≠ 0) :
    eW 1 0 ∈ W ∧ eW 2 0 ∈ W := by
  set A := Multiplicative.toAdd X with hA
  have hD1W : rho (c3, 1) X * X ∈ W := W.mul_mem (h1 X hXW) hXW
  have hD2W : rho (c3, 1) (rho (c3, 1) X * X) ∈ W := h1 _ hD1W
  have hD1 : Multiplicative.toAdd (rho (c3, 1) X * X) = c3m' * A + A := by
    rw [toAdd_mul, toAdd_rho_c3_one]
  have hD2 : Multiplicative.toAdd (rho (c3, 1) (rho (c3, 1) X * X)) = c3m' * (c3m' * A + A) := by
    rw [toAdd_rho_c3_one, hD1]
  have mem : ∀ B : Mat3, (B = c3m' * A + A ∨ B = c3m' * (c3m' * A + A) ∨
      B = (c3m' * A + A) + c3m' * (c3m' * A + A)) → Multiplicative.ofAdd B ∈ W := by
    rintro B (rfl | rfl | rfl)
    · rw [← hD1]
      exact hD1W
    · rw [← hD2]
      exact hD2W
    · have e : (c3m' * A + A) + c3m' * (c3m' * A + A) =
          Multiplicative.toAdd ((rho (c3, 1) X * X) * rho (c3, 1) (rho (c3, 1) X * X)) := by
        rw [toAdd_mul, hD1, hD2]
      rw [e, ofAdd_toAdd]
      exact W.mul_mem hD1W hD2W
  obtain ⟨e1, e2⟩ := col_of_c3m A hX5 hcol
  exact ⟨mem _ e1, mem _ e2⟩

theorem row_mem {W : Subgroup WMod} (h2 : ∀ X ∈ W, rho (1, c3) X ∈ W) {X : WMod} (hXW : X ∈ W)
    (hX5 : X ∈ V5)
    (hrow : Multiplicative.toAdd X 0 1 ≠ 0 ∨ Multiplicative.toAdd X 0 2 ≠ 0) :
    eW 0 1 ∈ W ∧ eW 0 2 ∈ W := by
  set A := Multiplicative.toAdd X with hA
  have hD1W : rho (1, c3) X * X ∈ W := W.mul_mem (h2 X hXW) hXW
  have hD2W : rho (1, c3) (rho (1, c3) X * X) ∈ W := h2 _ hD1W
  have hD1 : Multiplicative.toAdd (rho (1, c3) X * X) = A * c3m'ᵀ + A := by
    rw [toAdd_mul, toAdd_rho_one_c3]
  have hD2 : Multiplicative.toAdd (rho (1, c3) (rho (1, c3) X * X)) = (A * c3m'ᵀ + A) * c3m'ᵀ := by
    rw [toAdd_rho_one_c3, hD1]
  have mem : ∀ B : Mat3, (B = A * c3m'ᵀ + A ∨ B = (A * c3m'ᵀ + A) * c3m'ᵀ ∨
      B = (A * c3m'ᵀ + A) + (A * c3m'ᵀ + A) * c3m'ᵀ) → Multiplicative.ofAdd B ∈ W := by
    rintro B (rfl | rfl | rfl)
    · rw [← hD1]
      exact hD1W
    · rw [← hD2]
      exact hD2W
    · have e : (A * c3m'ᵀ + A) + (A * c3m'ᵀ + A) * c3m'ᵀ =
          Multiplicative.toAdd ((rho (1, c3) X * X) * rho (1, c3) (rho (1, c3) X * X)) := by
        rw [toAdd_mul, hD1, hD2]
      rw [e, ofAdd_toAdd]
      exact W.mul_mem hD1W hD2W
  obtain ⟨e1, e2⟩ := row_of_c3m A hX5 hrow
  exact ⟨mem _ e1, mem _ e2⟩

theorem det_mat_ne_zero (g : ↥SL32) : (mat g).det ≠ 0 := by
  have hu : IsUnit (mat g).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin 3) (ZMod 2)).isUnit
  exact hu.ne_zero

theorem row_ne_zero_of_not_mem_img {σ : MulAut WMod} (hσ : σ ∈ stabE) (hσi : σ ∉ img) :
    Multiplicative.toAdd (σ (eW 1 0)) 0 1 ≠ 0 ∨ Multiplicative.toAdd (σ (eW 1 0)) 0 2 ≠ 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_eq_rho_mul_tau hσ hσi
  obtain ⟨-, -, a0⟩ := (mulVec_e0_iff _).1 ha
  obtain ⟨b1, b2, -⟩ := (mulVec_e0_iff _).1 hb
  have htau : tau (eW 1 0) = eW 0 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_tau, toAdd_eW, toAdd_eW, Matrix.transpose_single]
  rw [MulAut.mul_apply, htau, toAdd_rho, toAdd_eW, mul_single01_mul_transpose,
    mul_single01_mul_transpose, a0, one_mul, one_mul]
  exact col_one_ne_zero (mat b) (det_mat_ne_zero b) b1 b2

theorem col_ne_zero_of_not_mem_img {σ : MulAut WMod} (hσ : σ ∈ stabE) (hσi : σ ∉ img) :
    Multiplicative.toAdd (σ (eW 0 1)) 1 0 ≠ 0 ∨ Multiplicative.toAdd (σ (eW 0 1)) 2 0 ≠ 0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_eq_rho_mul_tau hσ hσi
  obtain ⟨a1, a2, -⟩ := (mulVec_e0_iff _).1 ha
  obtain ⟨-, -, b0⟩ := (mulVec_e0_iff _).1 hb
  have htau : tau (eW 0 1) = eW 1 0 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_tau, toAdd_eW, toAdd_eW, Matrix.transpose_single]
  rw [MulAut.mul_apply, htau, toAdd_rho, toAdd_eW, mul_single10_mul_transpose,
    mul_single10_mul_transpose, b0, mul_one, mul_one]
  exact col_one_ne_zero (mat a) (det_mat_ne_zero a) a1 a2

theorem eW_mem_V5_row (j : Fin 3) : eW 0 j ∈ V5 := by
  fin_cases j <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem eW_mem_V5_col (i : Fin 3) : eW i 0 ∈ V5 := by
  fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide⟩

theorem V5_le_of_irred {W : Subgroup WMod} (hzW : eW 0 0 ∈ W) (hW5 : W ≤ V5) (hWz : ¬ W ≤ Z00)
    (h1 : ∀ X ∈ W, rho (c3, 1) X ∈ W) (h2 : ∀ X ∈ W, rho (1, c3) X ∈ W) {σ : MulAut WMod}
    (hσ : σ ∈ stabE) (hσi : σ ∉ img) (h3 : ∀ X ∈ W, σ X ∈ W) : V5 ≤ W := by
  obtain ⟨X, hXW, hXz⟩ := IsConcreteLE.not_le_iff_exists.mp hWz
  have hX5 := hW5 hXW
  have hcases : (Multiplicative.toAdd X 1 0 ≠ 0 ∨ Multiplicative.toAdd X 2 0 ≠ 0) ∨
      (Multiplicative.toAdd X 0 1 ≠ 0 ∨ Multiplicative.toAdd X 0 2 ≠ 0) := by
    by_contra h
    push Not at h
    obtain ⟨⟨c1, c2⟩, r1, r2⟩ := h
    exact hXz (mem_Z00_iff.2 (eq_zero_or_of_isV5 _ hX5 c1 c2 r1 r2))
  have hcol : eW 1 0 ∈ W ∧ eW 2 0 ∈ W ∧ eW 0 1 ∈ W ∧ eW 0 2 ∈ W := by
    rcases hcases with hc | hr
    · obtain ⟨e10, e20⟩ := col_mem h1 hXW hX5 hc
      obtain ⟨e01, e02⟩ := row_mem h2 (h3 _ e10)
        (map_mem_V5_of_mem_stabE hσ (eW_mem_V5_col 1)) (row_ne_zero_of_not_mem_img hσ hσi)
      exact ⟨e10, e20, e01, e02⟩
    · obtain ⟨e01, e02⟩ := row_mem h2 hXW hX5 hr
      obtain ⟨e10, e20⟩ := col_mem h1 (h3 _ e01)
        (map_mem_V5_of_mem_stabE hσ (eW_mem_V5_row 1)) (col_ne_zero_of_not_mem_img hσ hσi)
      exact ⟨e10, e20, e01, e02⟩
  obtain ⟨e10, e20, e01, e02⟩ := hcol
  intro Y hY
  have hY' := eq_of_isV5 _ hY
  have e : Y = Multiplicative.ofAdd (Multiplicative.toAdd Y 0 0 • Matrix.single 0 0 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd Y 0 1 • Matrix.single 0 1 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd Y 0 2 • Matrix.single 0 2 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd Y 1 0 • Matrix.single 1 0 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd Y 2 0 • Matrix.single 2 0 1) := by
    apply Multiplicative.toAdd.injective
    simpa only [toAdd_mul, toAdd_ofAdd] using hY'
  rw [e]
  exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (ofAdd_smul_mem _ hzW) (ofAdd_smul_mem _ e01))
    (ofAdd_smul_mem _ e02)) (ofAdd_smul_mem _ e10)) (ofAdd_smul_mem _ e20)

theorem eq_top_of_irred {W : Subgroup WMod} (h5W : V5 ≤ W) (hW : ¬ W ≤ V5)
    (h1 : ∀ X ∈ W, rho (c3, 1) X ∈ W) (h2 : ∀ X ∈ W, rho (1, c3) X ∈ W)
    (h3 : ∀ X ∈ W, rho (u0, 1) X ∈ W) : W = ⊤ := by
  obtain ⟨X, hXW, hX5⟩ := IsConcreteLE.not_le_iff_exists.mp hW
  have hb : blk2 (Multiplicative.toAdd X) ≠ 0 := fun h => hX5 ((isV5_iff_blk2 _).2 h)
  obtain ⟨X', hX'W, hb', hd'⟩ : ∃ X' ∈ W, blk2 (Multiplicative.toAdd X') ≠ 0 ∧
      (blk2 (Multiplicative.toAdd X')).det = 0 := by
    by_cases hd : (blk2 (Multiplicative.toAdd X)).det = 0
    · exact ⟨X, hXW, hb, hd⟩
    · refine ⟨rho (u0, 1) X * X, W.mul_mem (h3 X hXW) hXW, ?_⟩
      rw [toAdd_mul, toAdd_rho_u0_one]
      exact rank_one_of_u0m _ hb hd
  have hpow1 : ∀ n : ℕ, ∀ Y ∈ W, (rho (c3, 1)) ^ n • Y ∈ W := by
    intro n
    induction n with
    | zero => intro Y hY; simpa using hY
    | succ n ih => intro Y hY; rw [pow_succ', mul_smul]; exact h1 _ (ih Y hY)
  have hpow2 : ∀ n : ℕ, ∀ Y ∈ W, (rho (1, c3)) ^ n • Y ∈ W := by
    intro n
    induction n with
    | zero => intro Y hY; simpa using hY
    | succ n ih => intro Y hY; rw [pow_succ', mul_smul]; exact h2 _ (ih Y hY)
  have hgen : ∀ i j : ℕ, ∀ Y ∈ W, rho (c3 ^ i, c3 ^ j) Y ∈ W := by
    intro i j Y hY
    have e : rho (c3 ^ i, c3 ^ j) = rho (c3, 1) ^ i * rho (1, c3) ^ j := by
      rw [← map_pow, ← map_pow, ← map_mul, Prod.pow_mk, Prod.pow_mk, one_pow, one_pow,
        Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, MulAut.mul_apply]
    exact hpow1 i _ (hpow2 j Y hY)
  obtain ⟨i, j, hij⟩ := exists_c3_pow_blk _ hb' hd'
  have hY := hgen i j X' hX'W
  have h11 : eW 1 1 ∈ W := by
    have hV : rho (c3 ^ (i : ℕ), c3 ^ (j : ℕ)) X' * eW 1 1 ∈ V5 := by
      rw [mem_V5, toAdd_mul, toAdd_rho_pow, toAdd_eW]
      exact isV5_add_of_blk2 _ hij
    have := W.mul_mem (W.inv_mem hY) (h5W hV)
    simpa using this
  have h12 : eW 1 2 ∈ W := by
    have := h2 _ h11
    have e : rho (1, c3) (eW 1 1) = eW 1 2 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho_one_c3, toAdd_eW, toAdd_eW]
      exact single_c3m.1
    rwa [e] at this
  have h21 : eW 2 1 ∈ W := by
    have := h1 _ h11
    have e : rho (c3, 1) (eW 1 1) = eW 2 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho_c3_one, toAdd_eW, toAdd_eW]
      exact single_c3m.2.1
    rwa [e] at this
  have h22 : eW 2 2 ∈ W := by
    have := h1 _ (h2 _ h11)
    have e : rho (c3, 1) (rho (1, c3) (eW 1 1)) = eW 2 2 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho_c3_one, toAdd_rho_one_c3, toAdd_eW, toAdd_eW, ← Matrix.mul_assoc]
      exact single_c3m.2.2
    rwa [e] at this
  refine eq_top_iff.mpr fun Y _ => ?_
  set A := Multiplicative.toAdd Y with hA
  have hB : Multiplicative.ofAdd (A + blkPart A) ∈ W := h5W (isV5_add_blkPart A)
  have hP : Multiplicative.ofAdd (blkPart A) ∈ W := by
    unfold blkPart
    simp only [ofAdd_add]
    exact W.mul_mem (W.mul_mem (W.mul_mem (ofAdd_smul_mem _ h11) (ofAdd_smul_mem _ h12))
      (ofAdd_smul_mem _ h21)) (ofAdd_smul_mem _ h22)
  have hBB : blkPart A + blkPart A = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have e : Y = Multiplicative.ofAdd (A + blkPart A) * Multiplicative.ofAdd (blkPart A) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, add_assoc, hBB, add_zero]
  rw [e]
  exact W.mul_mem hB hP

@[expose] noncomputable def E9 : Subgroup (MulAut WMod) := (C3.prod C3).map rho

theorem E9_le_stabE : E9 ≤ stabE := by
  rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
  exact mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img g), rho_fix_E00 (C3_le_P1 hg1) (C3_le_P1 hg2)⟩

theorem card_E9 : Nat.card ↥E9 = 9 := by
  rw [E9, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_C3]

theorem card_stabE : Nat.card ↥stabE = 2 ^ 7 * 3 ^ 2 := by
  rw [← Nat.card_congr thetaEquiv.toEquiv, RegularWreathProduct.card, card_P1,
    Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))]
  rfl

theorem mem_C3 {g : ↥SL32} (hg : g ∈ C3) : ∃ i : Fin 3, g = c3 ^ (i : ℕ) := by
  classical
  rw [C3, mem_zpowers_iff_mem_range_orderOf, orderOf_c3] at hg
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hg
  exact ⟨⟨n, Finset.mem_range.mp hn⟩, rfl⟩

theorem exists_eq_of_mem_E9 {x : MulAut WMod} (hx : x ∈ E9) :
    ∃ i j : Fin 3, x = rho (c3 ^ (i : ℕ), c3 ^ (j : ℕ)) := by
  obtain ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩ := hx
  obtain ⟨i, rfl⟩ := mem_C3 hg
  obtain ⟨j, rfl⟩ := mem_C3 hh
  exact ⟨i, j, rfl⟩

@[expose] def ddW (x y : MulAut WMod) (X : WMod) : WMod :=
  x (y X * X⁻¹) * (y X * X⁻¹)⁻¹

theorem toAdd_ddW (i j k l : ℕ) (X : WMod) :
    Multiplicative.toAdd (ddW (rho (c3 ^ i, c3 ^ j)) (rho (c3 ^ k, c3 ^ l)) X) =
      dd i j k l (Multiplicative.toAdd X) := by
  unfold ddW dd
  rw [toAdd_mul, toAdd_inv, toAdd_rho_pow, toAdd_mul, toAdd_inv, toAdd_rho_pow, neg_eq_self',
    neg_eq_self']

theorem rho_c3_pow_eq_one_iff (i j : Fin 3) :
    rho (c3 ^ (i : ℕ), c3 ^ (j : ℕ)) = 1 → ((i : ℕ), (j : ℕ)) = (0, 0) := by
  intro h
  have h' := rho_injective (h.trans (map_one rho).symm)
  have hi : c3 ^ (i : ℕ) = 1 := congrArg Prod.fst h'
  have hj : c3 ^ (j : ℕ) = 1 := congrArg Prod.snd h'
  have hi' := orderOf_dvd_of_pow_eq_one hi
  have hj' := orderOf_dvd_of_pow_eq_one hj
  rw [orderOf_c3] at hi' hj'
  have := i.2
  have := j.2
  ext <;> simp <;> omega

theorem not_forall_of_mem_E9 {x y : MulAut WMod} (hx : x ∈ E9) (hy : y ∈ E9) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) :
    ¬ ((∀ X, ddW x y X ∈ V5) ∧ ∀ X ∈ V5, ddW x y X ∈ Z00) := by
  obtain ⟨i, j, rfl⟩ := exists_eq_of_mem_E9 hx
  obtain ⟨k, l, rfl⟩ := exists_eq_of_mem_E9 hy
  have hgen : (i : ℕ) * l % 3 ≠ (j : ℕ) * k % 3 := by
    intro h
    rcases dep_of_eq i j k l h with h0 | ⟨t, hk, hl⟩
    · apply hx1
      have hi : (i : ℕ) = 0 := congrArg Prod.fst h0
      have hj : (j : ℕ) = 0 := congrArg Prod.snd h0
      rw [hi, hj, pow_zero]
      exact map_one rho
    · apply hyx
      refine ⟨(t : ℕ), ?_⟩
      change rho (c3 ^ (i : ℕ), c3 ^ (j : ℕ)) ^ ((t : ℕ) : ℤ) = rho (c3 ^ (k : ℕ), c3 ^ (l : ℕ))
      rw [zpow_natCast, ← map_pow, Prod.pow_mk, ← pow_mul, ← pow_mul, hk, hl,
        ← pow_mod_orderOf c3 ((i : ℕ) * t), ← pow_mod_orderOf c3 ((j : ℕ) * t), orderOf_c3]
  rintro ⟨h1, h2⟩
  apply e9_facts i j k l hgen
  refine ⟨fun p q => ?_, fun p q hpq => ?_⟩
  · have := h1 (eW p q)
    rwa [mem_V5, toAdd_ddW, toAdd_eW] at this
  · have := h2 (eW p q) hpq
    rwa [mem_Z00_iff, toAdd_ddW, toAdd_eW] at this

theorem exists_not_mem_V5_of_mem_E9 {x : MulAut WMod} (hx : x ∈ E9) (hx1 : x ≠ 1) :
    ∃ X : WMod, x X * X⁻¹ ∉ V5 := by
  obtain ⟨i, j, rfl⟩ := exists_eq_of_mem_E9 hx
  obtain ⟨A, hA⟩ := e9_moves i j fun h => hx1 (by
    have hi : (i : ℕ) = 0 := congrArg Prod.fst h
    have hj : (j : ℕ) = 0 := congrArg Prod.snd h
    rw [hi, hj, pow_zero]
    exact map_one rho)
  refine ⟨Multiplicative.ofAdd A, fun h => hA ?_⟩
  rw [mem_V5, toAdd_mul, toAdd_inv, toAdd_rho_pow, neg_eq_self', toAdd_ofAdd] at h
  exact h

theorem exists_conj_mem_E9 {H : Subgroup (MulAut WMod)} (hH : H ≤ stabE) (hcard : Nat.card H = 9) :
    ∃ g ∈ stabE, ∀ x ∈ H, g * x * g⁻¹ ∈ E9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ^ (Nat.card ↥stabE).factorization 3 = 9 := by
    rw [card_stabE, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), zero_add,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
    norm_num
  have hH' : Nat.card ↥(H.subgroupOf stabE) = 3 ^ (Nat.card ↥stabE).factorization 3 := by
    rw [h3, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hE' : Nat.card ↥(E9.subgroupOf stabE) = 3 ^ (Nat.card ↥stabE).factorization 3 := by
    rw [h3, ← card_E9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe E9_le_stabE).toEquiv
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥stabE (Sylow.ofCard _ hH') (Sylow.ofCard _ hE')
  refine ⟨g, g.2, fun x hx => ?_⟩
  have h := congrArg (fun Q : Sylow 3 ↥stabE => (Q : Subgroup ↥stabE)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
  have hmem : (g * ⟨x, hH hx⟩ * g⁻¹ : ↥stabE) ∈ E9.subgroupOf stabE := by
    rw [← h]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨⟨x, hH hx⟩, hx, rfl⟩
  exact hmem

end L3Wr

end H

end CFSG.Quasithin
