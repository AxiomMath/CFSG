module

public import CFSG.Quasithin.Background.SmithB45LnL5Coeff
public import CFSG.Quasithin.Background.SmithB45LnRank
public import CFSG.Quasithin.Background.JonesParshallCurtisModels
public import CFSG.Quasithin.Background.JonesParshallCurtisBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45L5

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis
open CFSG.Quasithin.B45Ln (coordRep stackMat le_rank_of_submatrix eq_smul_of_rank)

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

@[expose] def conj5 : Representation (ZMod 2) G5 𝕄 where
  toFun g :=
    { toFun := fun X => (g : 𝕄) * X * ((g⁻¹ : G5) : 𝕄)
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := LinearMap.ext fun X => by
    change ((1 : G5) : 𝕄) * X * (((1 : G5)⁻¹ : G5) : 𝕄) = X
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
  map_mul' g h := LinearMap.ext fun X => by
    change ((g * h : G5) : 𝕄) * X * (((g * h)⁻¹ : G5) : 𝕄) =
      (g : 𝕄) * ((h : 𝕄) * X * ((h⁻¹ : G5) : 𝕄)) * ((g⁻¹ : G5) : 𝕄)
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_assoc]

theorem conj5_apply (g : G5) (X : 𝕄) : conj5 g X = (g : 𝕄) * X * ((g⁻¹ : G5) : 𝕄) := rfl

@[expose] def c24v (X : 𝕄) : Fin 24 → ZMod 2 :=
  ![X 0 1, X 0 2, X 0 3, X 0 4, X 1 0, X 1 2, X 1 3, X 1 4, X 2 0, X 2 1, X 2 3, X 2 4, X 3 0,
    X 3 1, X 3 2, X 3 4, X 4 0, X 4 1, X 4 2, X 4 3, X 0 0, X 1 1, X 2 2, X 3 3]

@[expose] def s24v (v : Fin 24 → ZMod 2) : 𝕄 :=
  !![v 20, v 0, v 1, v 2, v 3; v 4, v 21, v 5, v 6, v 7; v 8, v 9, v 22, v 10, v 11;
    v 12, v 13, v 14, v 23, v 15; v 16, v 17, v 18, v 19, v 20 + v 21 + v 22 + v 23]

@[expose] def c24 : 𝕄 →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := c24v
  map_add' X Y := by
    funext i
    fin_cases i <;> simp [c24v]
  map_smul' c X := by
    funext i
    fin_cases i <;> simp [c24v]

@[expose] def s24 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] 𝕄 where
  toFun := s24v
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s24v, add_add_add_comm]
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s24v, mul_add]

theorem c24_s24 (v : Fin 24 → ZMod 2) : c24 (s24 v) = v := by
  funext i
  fin_cases i <;> simp [c24, s24, c24v, s24v]

theorem trace_s24 (v : Fin 24 → ZMod 2) : (s24 v).trace = 0 := by
  have h0 : v 20 + v 20 = 0 := CharTwo.add_self_eq_zero _
  have h1 : v 21 + v 21 = 0 := CharTwo.add_self_eq_zero _
  have h2 : v 22 + v 22 = 0 := CharTwo.add_self_eq_zero _
  have h3 : v 23 + v 23 = 0 := CharTwo.add_self_eq_zero _
  simp [s24, s24v, Matrix.trace, Fin.sum_univ_five]
  linear_combination h0 + h1 + h2 + h3

theorem s24_c24 {X : 𝕄} (hX : X.trace = 0) : s24 (c24 X) = X := by
  simp only [Matrix.trace, Fin.sum_univ_five, Matrix.diag] at hX
  have h44 : X 4 4 + X 4 4 = 0 := CharTwo.add_self_eq_zero _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s24, c24, s24v, c24v]
  linear_combination hX - h44

theorem trace_conj5 (g : G5) (X : 𝕄) : (conj5 g X).trace = X.trace := by
  rw [conj5_apply, Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem c24_conj5_s24 (g h : G5) (v : Fin 24 → ZMod 2) :
    c24 (conj5 g (s24 (c24 (conj5 h (s24 v))))) = c24 (conj5 g (conj5 h (s24 v))) := by
  rw [s24_c24 (by rw [trace_conj5, trace_s24])]

@[expose] noncomputable def rep24 : Representation (ZMod 2) G5 (Fin 24 → ZMod 2) :=
  coordRep conj5 c24 s24 c24_s24 c24_conj5_s24

theorem rep24_apply (g : G5) (v : Fin 24 → ZMod 2) :
    rep24 g v = c24v ((g : 𝕄) * s24v v * ((g⁻¹ : G5) : 𝕄)) := rfl

@[expose] def mat24 (A : 𝕄) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  Matrix.of fun a j => c24v (A * s24v (Pi.single j 1) * A) a

theorem c24v_conj_eq (A : 𝕄) (v : Fin 24 → ZMod 2) :
    c24v (A * s24v v * A) = mat24 A *ᵥ v := by
  let f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
    c24.comp ((LinearMap.mulRight (ZMod 2) A).comp ((LinearMap.mulLeft (ZMod 2) A).comp s24))
  have hf : ∀ w, f w = c24v (A * s24v w * A) := fun w => rfl
  have hm : LinearMap.toMatrix' f = mat24 A := Matrix.ext fun a j => by
    rw [LinearMap.toMatrix'_apply, hf]
    rfl
  rw [← hf, ← LinearMap.toMatrix'_mulVec f v, hm]

theorem rep24_of_inv {g : G5} {A : 𝕄} (hgA : (g : 𝕄) = A) (hg : g * g = 1)
    (v : Fin 24 → ZMod 2) : rep24 g v = mat24 A *ᵥ v := by
  rw [rep24_apply, inv_eq_of_mul_eq_one_right hg, hgA, c24v_conj_eq]

@[expose] def y24 : Fin 24 → ZMod 2 :=
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem y24_ne : y24 ≠ 0 := by decide

theorem y24_conj {u : 𝕄} (hu : IsUpU u) : u * s24v y24 = s24v y24 ∧ s24v y24 * u = s24v y24 := by
  have h00 := (hu 0 0).2 rfl
  have h44 := (hu 4 4).2 rfl
  have h10 := (hu 1 0).1 (by decide)
  have h20 := (hu 2 0).1 (by decide)
  have h30 := (hu 3 0).1 (by decide)
  have h40 := (hu 4 0).1 (by decide)
  have h41 := (hu 4 1).1 (by decide)
  have h42 := (hu 4 2).1 (by decide)
  have h43 := (hu 4 3).1 (by decide)
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, s24v, y24, h00, h44, h10, h20, h30, h40, h41,
      h42, h43]

theorem y24_mem_fixU : y24 ∈ fixU rep24 := by
  intro u hu
  obtain ⟨h1, -⟩ := y24_conj (mem_Ugrp.mp hu)
  obtain ⟨-, h2⟩ := y24_conj (mem_Ugrp.mp (Ugrp.inv_mem hu))
  rw [rep24_apply, h1, h2]
  funext i
  fin_cases i <;> rfl

@[expose] def fixRows24 : Fin 23 → Fin 4 × Fin 24 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 9), (0, 13), (0, 17), (0, 20), (1, 1), (1, 5), (1, 6),
    (1, 7), (1, 14), (1, 18), (1, 21), (2, 2), (2, 10), (2, 11), (2, 19), (2, 22), (3, 3), (3, 15),
    (3, 23)]

@[expose] def fixCols24 : Fin 23 → Fin 24 :=
  ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def fixY24 : Matrix (Fin 23) (Fin 23) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1]

theorem rank_rep24 : 24 - 1 ≤ (stackMat fun s => mat24 (toMat (xB s))).rank :=
  le_rank_of_submatrix _ fixRows24 fixCols24 fixY24 (by decide +kernel)

theorem fix_y24 : ∀ s, mat24 (toMat (xB s)) *ᵥ y24 = y24 := by decide +kernel

theorem rep24_fix
    {x : Fin 24 → ZMod 2} (hx : x ∈ fixU rep24) : x = 0 ∨ x = y24 := by
  have hx' : ∀ s, mat24 (toMat (xB s)) *ᵥ x = x := fun s => by
    rw [← rep24_of_inv (xM_eq_toMat s) (xE_mul_self s)]
    exact hx _ (xE_mem s)
  obtain ⟨c, rfl⟩ := eq_smul_of_rank rank_rep24 y24_ne fix_y24 hx'
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · left
    rw [zero_smul]
  · right
    rw [one_smul]

@[expose] def gen24 : Fin 24 → BM :=
  ![![2, 17, 24, 20, 27], ![1, 10, 22, 21, 12], ![27, 6, 20, 12, 22], ![17, 9, 15, 4, 12],
    ![13, 8, 7, 26, 6], ![20, 26, 31, 30, 29], ![17, 19, 15, 22, 18], ![10, 6, 25, 18, 4],
    ![5, 1, 2, 16, 24], ![26, 5, 9, 20, 16], ![29, 6, 19, 2, 20], ![8, 10, 27, 4, 22],
    ![22, 8, 4, 3, 24], ![14, 23, 28, 19, 16], ![20, 3, 25, 12, 10], ![23, 2, 14, 24, 4],
    ![29, 3, 22, 9, 7], ![21, 17, 9, 29, 14], ![6, 8, 24, 28, 19], ![2, 21, 4, 15, 12],
    ![26, 1, 23, 30, 3], ![6, 8, 22, 18, 17], ![24, 11, 13, 17, 1], ![24, 25, 16, 31, 5]]

@[expose] def gen24I : Fin 24 → BM :=
  ![![21, 1, 31, 19, 23], ![1, 13, 31, 15, 22], ![25, 20, 22, 30, 18], ![26, 14, 8, 24, 27],
    ![20, 7, 23, 2, 13], ![12, 20, 10, 29, 11], ![18, 3, 24, 13, 19], ![13, 18, 16, 19, 26],
    ![2, 4, 3, 24, 8], ![26, 15, 24, 30, 16], ![22, 8, 10, 7, 26], ![29, 3, 8, 1, 27],
    ![31, 23, 4, 2, 18], ![13, 21, 10, 30, 16], ![13, 15, 23, 31, 22], ![13, 2, 16, 22, 30],
    ![15, 13, 18, 7, 27], ![13, 26, 3, 9, 15], ![27, 13, 12, 2, 6], ![25, 1, 4, 20, 31],
    ![2, 18, 9, 14, 29], ![21, 13, 12, 2, 5], ![16, 11, 13, 25, 24], ![3, 25, 19, 5, 4]]

@[expose] def binv24 : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0;
    1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0;
    0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1;
    1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0;
    1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0;
    0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1;
    1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0;
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1;
    1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0;
    1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0]

theorem gen24_inv : ∀ i, bmul (gen24 i) (gen24I i) = bone ∧ bmul (gen24I i) (gen24 i) = bone := by
  decide +kernel

theorem gen24_basis :
    Matrix.of (fun a i => c24v (toMat (gen24 i) * s24v y24 * toMat (gen24I i)) a) * binv24 = 1 := by
  decide +kernel

theorem orbitSpan_top_of_mul {n : ℕ} (ρ : Representation (ZMod 2) G5 (Fin n → ZMod 2))
    (x : Fin n → ZMod 2) (v : Fin n → Fin n → ZMod 2) (hv : ∀ i, v i ∈ orbitSpan ρ x)
    (Y : Matrix (Fin n) (Fin n) (ZMod 2)) (hY : Matrix.of (fun a i => v i a) * Y = 1) :
    orbitSpan ρ x = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, (Y *ᵥ w) i • v i := by
    have h1 : (Matrix.of (fun a i => v i a) * Y) *ᵥ w = w := by rw [hY, one_mulVec]
    rw [← mulVec_mulVec] at h1
    conv_lhs => rw [← h1]
    funext a
    simp only [mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hw]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv i)

theorem rep24_gen : orbitSpan rep24 y24 = ⊤ := by
  have hG : ∀ i, toMat (gen24 i) * toMat (gen24I i) = 1 := fun i => by
    rw [← toMat_bmul, (gen24_inv i).1, toMat_bone]
  have hG' : ∀ i, toMat (gen24I i) * toMat (gen24 i) = 1 := fun i => by
    rw [← toMat_bmul, (gen24_inv i).2, toMat_bone]
  refine orbitSpan_top_of_mul rep24 y24
    (fun i => c24v (toMat (gen24 i) * s24v y24 * toMat (gen24I i))) (fun i => ?_) binv24
    gen24_basis
  have e : rep24 (B42Ln.ofMatInv _ _ (hG i)) y24 =
      c24v (toMat (gen24 i) * s24v y24 * toMat (gen24I i)) := by
    rw [rep24_apply, B42Ln.inv_ofMatInv (hG i) (hG' i)]
    rfl
  rw [← e]
  exact Submodule.subset_span ⟨_, rfl⟩

theorem rep24_simple :
    IsSimpleRep rep24 :=
  isSimpleRep_of_fixU rep24 (fun _ hx => rep24_fix hx) rep24_gen

@[expose] def J24 : Fin 4 → Bool := ![false, true, true, false]

theorem rep24_Th_checks : ∀ s : Fin 4,
    mat24 (toMat (yB s)) *ᵥ y24 + mat24 (toMat (xB s)) *ᵥ (mat24 (toMat (yB s)) *ᵥ y24) =
      if J24 s then 0 else y24 := by
  decide +kernel

theorem rep24_type (s : Fin 4) :
    Th rep24 s y24 = 0 ↔ J24 s = true := by
  rw [Th_apply, map_mul, Module.End.mul_apply, rep24_of_inv (yM_eq_toMat s) (yE_mul_self s),
    rep24_of_inv (xM_eq_toMat s) (xE_mul_self s), rep24_Th_checks]
  cases J24 s
  · simp [y24_ne]
  · simp

theorem iso_rep24
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) G5 V} (hρ : IsSimpleRep ρ) {y : V} (hy : y ∈ fixU ρ)
    (hy0 : y ≠ 0) (hJ : ∀ s, Th ρ s y = 0 ↔ J24 s = true) :
    ∃ β : V ≃ₗ[ZMod 2] (Fin 24 → ZMod 2), ∀ g v, β (ρ g v) = rep24 g (β v) :=
  iso_of_type hρ rep24_simple hy hy0 y24_mem_fixU y24_ne fun s => (hJ s).trans (rep24_type s).symm

end CFSG.Quasithin.B45L5
