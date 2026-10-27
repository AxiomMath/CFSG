module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aLocal
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.Quasithin.B45U3

open CFSG.QuasithinUnique.Setup.X7a CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open scoped MatrixGroups Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {s : ℕ}

omit [Finite K] [CharP K 2] in
theorem antidiag_three : (antidiag 3 : Matrix (Fin 3) (Fin 3) K) = wJMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, wJMat]

variable (K s) in
@[expose] noncomputable def suJ : Subgroup SL(3, K) :=
  (SU (unitaryInvolution K 2 s) 3).comap Matrix.SpecialLinearGroup.toGL

theorem mem_suJ {g : SL(3, K)} :
    g ∈ suJ K s ↔ ((g : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K 2 s))ᵀ * wJMat *
      (g : Matrix (Fin 3) (Fin 3) K) = wJMat := by
  rw [suJ, Subgroup.mem_comap, mem_SU, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, conjTr,
    antidiag_three]
  exact and_iff_right g.2

theorem suJ_entry {g : SL(3, K)} (hg : g ∈ suJ K s) (i j : Fin 3) :
    ((g : Matrix (Fin 3) (Fin 3) K) 0 i) ^ 2 ^ s * (g : Matrix (Fin 3) (Fin 3) K) 2 j +
      ((g : Matrix (Fin 3) (Fin 3) K) 1 i) ^ 2 ^ s * (g : Matrix (Fin 3) (Fin 3) K) 1 j +
      ((g : Matrix (Fin 3) (Fin 3) K) 2 i) ^ 2 ^ s * (g : Matrix (Fin 3) (Fin 3) K) 0 j =
      (wJMat : Matrix (Fin 3) (Fin 3) K) i j := by
  have h := congrFun (congrFun (mem_suJ.mp hg) i) j
  rw [← h]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
    wJMat, unitaryInvolution_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem wJ_mem_suJ : (wJ : SL(3, K)) ∈ suJ K s := by
  rw [mem_suJ, wJ_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def wJs : suJ K s := ⟨wJ, wJ_mem_suJ⟩

theorem coe_wJs : ((wJs : suJ K s) : SL(3, K)) = wJ := rfl

theorem wJs_mul_self : (wJs : suJ K s) * wJs = 1 :=
  Subtype.ext wJ_mul_self

theorem wJs_inv : (wJs : suJ K s)⁻¹ = wJs :=
  inv_eq_of_mul_eq_one_right wJs_mul_self

section Unitri

variable (hK : Nat.card K = (2 ^ s) ^ 2)
include hK

omit hK in
theorem eq_of_u3_mem_suJ {x y z : K} (h : u3 x y z ∈ suJ K s) :
    z = x ^ 2 ^ s ∧ y + y ^ 2 ^ s = x * x ^ 2 ^ s := by
  have h0 := suJ_entry h 0 0
  have h1 := suJ_entry h 0 1
  simp only [u3_coe, u3Mat, wJMat] at h0 h1
  simp at h0 h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨by linear_combination h1 - (x ^ 2 ^ s) * h2,
    by linear_combination h0 - x * x ^ 2 ^ s * h2⟩

theorem u3_mem_suJ {x y : K} (h : y + y ^ 2 ^ s = x * x ^ 2 ^ s) :
    u3 x y (x ^ 2 ^ s) ∈ suJ K s := by
  have hσ : ∀ c : K, (c ^ 2 ^ s) ^ 2 ^ s = c := fun c => by
    have := unitaryInvolution_involutive hK c
    rwa [unitaryInvolution_apply, unitaryInvolution_apply] at this
  rw [mem_suJ, u3_coe]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u3Mat, wJMat, Matrix.mul_apply, Fin.sum_univ_three, iterateFrobenius_def, hσ]
  · linear_combination h + x * x ^ 2 ^ s * h2
  · linear_combination x ^ 2 ^ s * h2
  · linear_combination x * h2

omit hK [Finite K] in
theorem up3_eq_wJ_mul (x y z : K) : up3 x y z = wJ * u3 x y z * wJ := (wJ_u3_wJ x y z).symm

omit hK [Finite K] in
theorem u3_eq_wJ_mul (x y z : K) : u3 x y z = wJ * up3 x y z * wJ := by
  rw [up3_eq_wJ_mul, ← mul_assoc, ← mul_assoc, wJ_mul_self, one_mul, mul_assoc, wJ_mul_self,
    mul_one]

omit hK in
theorem eq_of_up3_mem_suJ {x y z : K} (h : up3 x y z ∈ suJ K s) :
    z = x ^ 2 ^ s ∧ y + y ^ 2 ^ s = x * x ^ 2 ^ s := by
  refine eq_of_u3_mem_suJ ?_
  rw [u3_eq_wJ_mul]
  exact mul_mem (mul_mem wJ_mem_suJ h) wJ_mem_suJ

theorem up3_mem_suJ {x y : K} (h : y + y ^ 2 ^ s = x * x ^ 2 ^ s) :
    up3 x y (x ^ 2 ^ s) ∈ suJ K s := by
  rw [up3_eq_wJ_mul]
  exact mul_mem (mul_mem wJ_mem_suJ (u3_mem_suJ hK h)) wJ_mem_suJ

omit [Finite K] [CharP K 2] in
theorem units_pow_sq_sub_one (r : Kˣ) : r ^ ((2 ^ s) ^ 2 - 1) = 1 := by
  have h := pow_card_eq_one' (G := Kˣ) (x := r)
  rwa [Nat.card_units, hK] at h

theorem dT_mem_suJ (r : Kˣ) : dT r (r ^ (2 ^ s - 1)) ∈ suJ K s := by
  have hq : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hrq : r * r ^ (2 ^ s - 1) = r ^ 2 ^ s := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  have hsq := units_pow_sq_sub_one hK r
  have e1 : (r ^ (2 ^ s - 1)) ^ 2 ^ s * r ^ (2 ^ s - 1) = 1 := by
    rw [← pow_mul, ← pow_add]
    convert hsq using 2
    zify [hq, Nat.one_le_pow 2 (2 ^ s) (by positivity)]
    ring
  have e2 : (r ^ 2 ^ s)⁻¹ ^ 2 ^ s * r = 1 := by
    have : (r ^ 2 ^ s) ^ 2 ^ s = r := by
      rw [← pow_mul, ← sq]
      have h1 : (2 ^ s) ^ 2 = (2 ^ s) ^ 2 - 1 + 1 := by
        have := Nat.one_le_pow 2 (2 ^ s) (by positivity)
        omega
      rw [h1, pow_succ, hsq, one_mul]
    rw [inv_pow, this, inv_mul_cancel]
  rw [mem_suJ, dT_coe]
  simp only [dTMat]
  rw [hrq]
  have e1' := congrArg (fun u : Kˣ => (u : K)) e1
  have e2' := congrArg (fun u : Kˣ => (u : K)) e2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, Units.val_inv_eq_inv_val]
    at e1' e2'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three, iterateFrobenius_def]
  · exact e1'
  · rw [← inv_pow]
    exact e2'

@[expose] noncomputable def hJ : Kˣ →* suJ K s where
  toFun r := ⟨dT r (r ^ (2 ^ s - 1)), dT_mem_suJ hK r⟩
  map_one' := Subtype.ext (by simp only [one_pow, dT_one]; rfl)
  map_mul' r r' := Subtype.ext (by
    simp only [Subgroup.coe_mul, dT_mul, mul_pow])

theorem coe_hJ (r : Kˣ) : ((hJ hK r : suJ K s) : SL(3, K)) = dT r (r ^ (2 ^ s - 1)) := rfl

end Unitri

variable (K s) in
@[expose] noncomputable def UJ : Subgroup (suJ K s) := (upperUni K).subgroupOf (suJ K s)

variable (K s) in
@[expose] noncomputable def LJ : Subgroup (suJ K s) := (lowerUni K).subgroupOf (suJ K s)

variable (K s) in
@[expose] noncomputable def HJ (hK : Nat.card K = (2 ^ s) ^ 2) : Subgroup (suJ K s) :=
  (hJ hK).range

theorem mem_UJ {u : suJ K s} : u ∈ UJ K s ↔ (u : SL(3, K)) ∈ upperUni K := Iff.rfl

theorem mem_LJ {l : suJ K s} : l ∈ LJ K s ↔ (l : SL(3, K)) ∈ lowerUni K := Iff.rfl

theorem exists_of_mem_UJ {u : suJ K s} (hu : u ∈ UJ K s) :
    ∃ x y : K, y + y ^ 2 ^ s = x * x ^ 2 ^ s ∧ (u : SL(3, K)) = up3 x y (x ^ 2 ^ s) := by
  obtain ⟨x, y, z, hxyz⟩ := mem_upperUni.mp (mem_UJ.mp hu)
  have h := u.2
  rw [hxyz] at h
  obtain ⟨rfl, h2⟩ := eq_of_up3_mem_suJ h
  exact ⟨x, y, h2, hxyz⟩

theorem exists_of_mem_LJ {l : suJ K s} (hl : l ∈ LJ K s) :
    ∃ x y : K, y + y ^ 2 ^ s = x * x ^ 2 ^ s ∧ (l : SL(3, K)) = u3 x y (x ^ 2 ^ s) := by
  obtain ⟨x, y, z, hxyz⟩ := mem_lowerUni.mp (mem_LJ.mp hl)
  have h := l.2
  rw [hxyz] at h
  obtain ⟨rfl, h2⟩ := eq_of_u3_mem_suJ h
  exact ⟨x, y, h2, hxyz⟩

theorem UJ_inf_LJ : UJ K s ⊓ LJ K s = ⊥ := by
  rw [eq_bot_iff]
  intro g ⟨hu, hl⟩
  obtain ⟨x, y, z, h1⟩ := mem_upperUni.mp (mem_UJ.mp hu)
  obtain ⟨x', y', z', h2⟩ := mem_lowerUni.mp (mem_LJ.mp hl)
  have e : up3 x y z = u3 x' y' z' := h1.symm.trans h2
  have e' : upMat x y z = u3Mat x' y' z' := by rw [← up3_coe, ← u3_coe, e]
  have hx := congrFun (congrFun e' 1) 2
  have hy := congrFun (congrFun e' 0) 2
  have hz := congrFun (congrFun e' 0) 1
  simp [upMat, u3Mat] at hx hy hz
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [h1, hx, hy, hz, up3_zero]
  rfl

theorem wJs_conj_LJ {l : suJ K s} (hl : l ∈ LJ K s) : wJs * l * wJs⁻¹ ∈ UJ K s := by
  rw [mem_UJ, wJs_inv]
  obtain ⟨x, y, z, h⟩ := mem_lowerUni.mp (mem_LJ.mp hl)
  show wJ * (l : SL(3, K)) * wJ ∈ upperUni K
  rw [h, wJ_u3_wJ]
  exact mem_upperUni.mpr ⟨x, y, z, rfl⟩

theorem wJs_conj_UJ {u : suJ K s} (hu : u ∈ UJ K s) : wJs * u * wJs⁻¹ ∈ LJ K s := by
  rw [mem_LJ, wJs_inv]
  obtain ⟨x, y, z, h⟩ := mem_upperUni.mp (mem_UJ.mp hu)
  show wJ * (u : SL(3, K)) * wJ ∈ lowerUni K
  rw [h, up3_eq_wJ_mul, ← mul_assoc, ← mul_assoc, wJ_mul_self, one_mul, mul_assoc, wJ_mul_self,
    mul_one]
  exact mem_lowerUni.mpr ⟨x, y, z, rfl⟩

omit [Finite K] [CharP K 2] in
theorem dT_conj_up3 (r t : Kˣ) (x y z : K) :
    (dT r t : SL(3, K)) * up3 x y z * (dT r t)⁻¹ =
      up3 ((t : K) * x * ((r * t : Kˣ) : K)) ((r : K) * y * ((r * t : Kˣ) : K))
        ((r : K) * z * ((t⁻¹ : Kˣ) : K)) := by
  rw [dT_inv]
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, dT_coe, up3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dTMat, upMat, Matrix.mul_apply, Fin.sum_univ_three, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;> field_simp

omit [Finite K] [CharP K 2] in
theorem dT_conj_u3 (r t : Kˣ) (x y z : K) :
    (dT r t : SL(3, K)) * u3 x y z * (dT r t)⁻¹ =
      u3 ((t : K) * x * ((r⁻¹ : Kˣ) : K)) (((r * t)⁻¹ : Kˣ) * y * ((r⁻¹ : Kˣ) : K))
        (((r * t)⁻¹ : Kˣ) * z * ((t⁻¹ : Kˣ) : K)) := by
  rw [dT_inv]
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, dT_coe, u3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dTMat, u3Mat, Matrix.mul_apply, Fin.sum_univ_three, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]
  field_simp

theorem HJ_conj_UJ (hK : Nat.card K = (2 ^ s) ^ 2) {h u : suJ K s} (hh : h ∈ HJ K s hK)
    (hu : u ∈ UJ K s) :
    h * u * h⁻¹ ∈ UJ K s := by
  obtain ⟨r, rfl⟩ := hh
  obtain ⟨x, y, z, hxyz⟩ := mem_upperUni.mp (mem_UJ.mp hu)
  rw [mem_UJ]
  show ((hJ hK r : suJ K s) : SL(3, K)) * u * ((hJ hK r : suJ K s) : SL(3, K))⁻¹ ∈ upperUni K
  rw [coe_hJ, hxyz, dT_conj_up3]
  exact mem_upperUni.mpr ⟨_, _, _, rfl⟩

theorem HJ_conj_LJ (hK : Nat.card K = (2 ^ s) ^ 2) {h l : suJ K s} (hh : h ∈ HJ K s hK)
    (hl : l ∈ LJ K s) :
    h * l * h⁻¹ ∈ LJ K s := by
  obtain ⟨r, rfl⟩ := hh
  obtain ⟨x, y, z, hxyz⟩ := mem_lowerUni.mp (mem_LJ.mp hl)
  rw [mem_LJ]
  show ((hJ hK r : suJ K s) : SL(3, K)) * l * ((hJ hK r : suJ K s) : SL(3, K))⁻¹ ∈ lowerUni K
  rw [coe_hJ, hxyz, dT_conj_u3]
  exact mem_lowerUni.mpr ⟨_, _, _, rfl⟩

theorem HJ_comm (hK : Nat.card K = (2 ^ s) ^ 2) {a b : suJ K s} (ha : a ∈ HJ K s hK)
    (hb : b ∈ HJ K s hK) : a * b = b * a := by
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨r', rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem wJs_conj_hJ (hK : Nat.card K = (2 ^ s) ^ 2) (r : Kˣ) :
    wJs * hJ hK r * wJs⁻¹ = hJ hK (r ^ 2 ^ s)⁻¹ := by
  have hq : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hsq := units_pow_sq_sub_one hK r
  have hrq : r * r ^ (2 ^ s - 1) = r ^ 2 ^ s := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  have e1 : ((r ^ 2 ^ s)⁻¹) ^ (2 ^ s - 1) = r ^ (2 ^ s - 1) := by
    rw [inv_pow, ← pow_mul, inv_eq_iff_mul_eq_one, ← pow_add]
    convert hsq using 2
    zify [hq, Nat.one_le_pow 2 (2 ^ s) (by positivity)]
    ring
  have e2 : ((r ^ 2 ^ s)⁻¹ * r ^ (2 ^ s - 1))⁻¹ = r := by
    rw [← hrq, mul_inv_rev, inv_inv, mul_comm r, ← mul_assoc, inv_mul_cancel, one_mul]
  apply Subtype.ext
  apply Subtype.ext
  rw [wJs_inv]
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_wJs, coe_hJ, wJ_coe,
    dT_coe]
  rw [e1]
  simp only [dTMat]
  rw [hrq, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three]

section Card

variable (hK : Nat.card K = (2 ^ s) ^ 2)
include hK

theorem card_heisPairs :
    Nat.card {p : K × K // p.2 + p.2 ^ 2 ^ s = p.1 * p.1 ^ 2 ^ s} = (2 ^ s) ^ 3 := by
  set σ := unitaryInvolution K 2 s
  have hσ : ∀ c : K, σ c = c ^ 2 ^ s := unitaryInvolution_apply K 2 s
  have htr : ∀ x : K, ∃ c : K, c + σ c = x * σ x := fun x =>
    exists_add_unitaryInvolution_eq hK (by
      rw [map_mul, unitaryInvolution_involutive hK, mul_comm])
  choose c hc using htr
  let e : {p : K × K // p.2 + p.2 ^ 2 ^ s = p.1 * p.1 ^ 2 ^ s} ≃ K × traceZero σ :=
    { toFun := fun p => (p.1.1, ⟨p.1.2 - c p.1.1, by
        rw [mem_traceZero, map_sub, hσ (p.1.2)]
        have h1 := p.2
        have h2 := hc p.1.1
        rw [hσ p.1.1] at h2
        linear_combination h1 - h2⟩)
      invFun := fun az => ⟨(az.1, az.2 + c az.1), by
        have h1 := (mem_traceZero σ).1 az.2.2
        have h2 := hc az.1
        show (az.2 : K) + c az.1 + (az.2 + c az.1) ^ 2 ^ s = az.1 * az.1 ^ 2 ^ s
        rw [← hσ, ← hσ, map_add]
        linear_combination h1 + h2⟩
      left_inv := fun p => by
        apply Subtype.ext
        simp
      right_inv := fun az => by
        ext
        · rfl
        · simp }
  rw [Nat.card_congr e, Nat.card_prod, hK, CFSG.LieType.Steinberg.card_traceZero hK]
  ring

theorem card_LJ : Nat.card (LJ K s) = (2 ^ s) ^ 3 := by
  rw [← card_heisPairs hK]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : {p : K × K // p.2 + p.2 ^ 2 ^ s = p.1 * p.1 ^ 2 ^ s} =>
      (⟨⟨u3 p.1.1 p.1.2 (p.1.1 ^ 2 ^ s), u3_mem_suJ hK p.2⟩,
        mem_lowerUni.mpr ⟨_, _, _, rfl⟩⟩ : LJ K s)) ⟨?_, ?_⟩)).symm
  · intro p p' h
    have h1 := u3_inj (congrArg (fun l : LJ K s => ((l : suJ K s) : SL(3, K))) h)
    exact Subtype.ext (Prod.ext h1.1 h1.2.1)
  · intro l
    obtain ⟨x, y, hxy, hl⟩ := exists_of_mem_LJ l.2
    exact ⟨⟨(x, y), hxy⟩, Subtype.ext (Subtype.ext hl.symm)⟩

theorem card_UJ : Nat.card (UJ K s) = (2 ^ s) ^ 3 := by
  rw [← card_heisPairs hK]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : {p : K × K // p.2 + p.2 ^ 2 ^ s = p.1 * p.1 ^ 2 ^ s} =>
      (⟨⟨up3 p.1.1 p.1.2 (p.1.1 ^ 2 ^ s), up3_mem_suJ hK p.2⟩,
        mem_upperUni.mpr ⟨_, _, _, rfl⟩⟩ : UJ K s)) ⟨?_, ?_⟩)).symm
  · intro p p' h
    have h1 := up3_inj (congrArg (fun u : UJ K s => ((u : suJ K s) : SL(3, K))) h)
    exact Subtype.ext (Prod.ext h1.1 h1.2.1)
  · intro u
    obtain ⟨x, y, hxy, hu⟩ := exists_of_mem_UJ u.2
    exact ⟨⟨(x, y), hxy⟩, Subtype.ext (Subtype.ext hu.symm)⟩

theorem isPGroup_UJ : IsPGroup 2 (UJ K s) :=
  IsPGroup.of_card (n := 3 * s) (by rw [card_UJ hK, ← pow_mul, mul_comm])

theorem isPGroup_LJ : IsPGroup 2 (LJ K s) :=
  IsPGroup.of_card (n := 3 * s) (by rw [card_LJ hK, ← pow_mul, mul_comm])

end Card

omit [Finite K] in
theorem upMat_mul_wJMat {a A b B : K} (hb : b ≠ 0) (hB : B ≠ 0) (h : b + B = a * A) :
    upMat a b A * wJMat =
      u3Mat (a / b) (1 / b) (A / B) * !![b, 0, 0; 0, B / b, 0; 0, 0, 1 / B] *
        upMat (a / B) (1 / b) (A / b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upMat, u3Mat, wJMat, Matrix.mul_apply, Fin.sum_univ_three, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff]
  all_goals field_simp
  · linear_combination h - B * h2
  · linear_combination (-a) * h2
  · linear_combination (-A) * h2
  · linear_combination -h - a * A * h2

omit [Finite K] [CharP K 2] in
theorem dTMat_mk0 {b : K} (hb : b ≠ 0) :
    dTMat (Units.mk0 b hb) (Units.mk0 b hb ^ (2 ^ s - 1)) =
      !![b, 0, 0; 0, b ^ 2 ^ s / b, 0; 0, 0, 1 / b ^ 2 ^ s] := by
  have hq : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have e : b ^ (2 ^ s - 1) = b ^ 2 ^ s / b := by
    rw [pow_sub₀ b hb hq, pow_one, div_eq_mul_inv]
  have e' : b * b ^ (2 ^ s - 1) = b ^ 2 ^ s := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dTMat, e]
  field_simp

omit [Finite K] in
theorem up3_mul_wJ {a b : K} (hb : b ≠ 0) (h : b + b ^ 2 ^ s = a * a ^ 2 ^ s) :
    up3 a b (a ^ 2 ^ s) * wJ =
      u3 (a / b) (1 / b) (a ^ 2 ^ s / b ^ 2 ^ s) *
        dT (Units.mk0 b hb) (Units.mk0 b hb ^ (2 ^ s - 1)) *
          up3 (a / b ^ 2 ^ s) (1 / b) (a ^ 2 ^ s / b) := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, up3_coe, u3_coe, wJ_coe, dT_coe, dTMat_mk0]
  exact upMat_mul_wJMat hb (pow_ne_zero _ hb) h

omit [Finite K] [CharP K 2] in
theorem dT_mul_apply (r t : Kˣ) (g : SL(3, K)) (i j : Fin 3) :
    ((dT r t * g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i j =
      ![(r : K), (t : K), (((r * t)⁻¹ : Kˣ) : K)] i * (g : Matrix (Fin 3) (Fin 3) K) i j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, dT_coe]
  fin_cases i <;> simp [dTMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_HJ_UJ_of_col (hK : Nat.card K = (2 ^ s) ^ 2) {g : suJ K s}
    (h10 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) :
    ∃ h ∈ HJ K s hK, ∃ u ∈ UJ K s, g = h * u := by
  have hdet := (g : SL(3, K)).2
  rw [Matrix.det_fin_three, h10, h20] at hdet
  have h00 : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  set r : Kˣ := Units.mk0 _ h00 with hr
  refine ⟨hJ hK r, ⟨r, rfl⟩, (hJ hK r)⁻¹ * g, ?_, by group⟩
  set u : suJ K s := (hJ hK r)⁻¹ * g with hu
  have hucoe : (u : SL(3, K)) = dT r⁻¹ (r ^ (2 ^ s - 1))⁻¹ * (g : SL(3, K)) := by
    rw [hu, Subgroup.coe_mul, Subgroup.coe_inv, coe_hJ, dT_inv]
  have hent : ∀ i j, ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i j =
      ![((r⁻¹ : Kˣ) : K), (((r ^ (2 ^ s - 1))⁻¹ : Kˣ) : K),
        (((r⁻¹ * (r ^ (2 ^ s - 1))⁻¹)⁻¹ : Kˣ) : K)] i *
        ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    rw [hucoe, dT_mul_apply]
  have hu00 : ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    rw [hent]
    simp [hr, h00]
  have hu10 : ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    rw [hent, h10, mul_zero]
  have hu20 : ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    rw [hent, h20, mul_zero]
  have hrow : ∀ j, ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 j =
      (wJMat : Matrix (Fin 3) (Fin 3) K) 0 j := by
    intro j
    have := suJ_entry u.2 0 j
    rw [hu00, hu10, hu20] at this
    simpa using this
  have hu21 : ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    rw [hrow]; simp [wJMat]
  have hu22 : ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    rw [hrow]; simp [wJMat]
  have hudet := (u : SL(3, K)).2
  rw [Matrix.det_fin_three, hu00, hu10, hu20, hu21, hu22] at hudet
  have hu11 : ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    linear_combination hudet
  rw [mem_UJ, mem_upperUni]
  refine ⟨((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 2,
    ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2,
    ((u : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 1, Subtype.ext ?_⟩
  rw [up3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upMat, hu00, hu10, hu20, hu21, hu22, hu11]

theorem suJ_cover (hK : Nat.card K = (2 ^ s) ^ 2) (g : suJ K s) :
    (∃ l ∈ LJ K s, ∃ h ∈ HJ K s hK, ∃ u ∈ UJ K s, g = l * (h * u)) ∨
      ∃ h ∈ HJ K s hK, ∃ u ∈ UJ K s, g = wJs * (h * u) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set G := ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) with hG
  have hiso := suJ_entry g.2 0 0
  rw [← hG] at hiso
  simp only [wJMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hiso
  by_cases h00 : G 0 0 = 0
  · right
    have h10 : G 1 0 = 0 := by
      rw [h00, zero_pow (pow_ne_zero _ two_ne_zero), zero_mul, mul_zero, zero_add,
        add_zero] at hiso
      have : G 1 0 ^ (2 ^ s + 1) = 0 := by rw [pow_succ']; linear_combination hiso
      exact (pow_eq_zero_iff (Nat.succ_ne_zero _)).mp this
    have hw : ∀ i j, (((wJs * g : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i j =
        G (Fin.rev i) j := by
      intro i j
      rw [Subgroup.coe_mul, coe_wJs, Matrix.SpecialLinearGroup.coe_mul, wJ_coe]
      fin_cases i <;> simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three, hG]
    obtain ⟨h, hh, u, hu, e⟩ := exists_HJ_UJ_of_col hK (g := wJs * g)
      (by rw [hw]; exact h10) (by rw [hw]; exact h00)
    refine ⟨h, hh, u, hu, ?_⟩
    rw [← e, ← mul_assoc, wJs_mul_self, one_mul]
  · left
    obtain ⟨X, hX⟩ : ∃ X : K, X * G 0 0 = G 1 0 := ⟨G 1 0 / G 0 0, by field_simp⟩
    obtain ⟨Y, hY⟩ : ∃ Y : K, Y * G 0 0 = G 2 0 := ⟨G 2 0 / G 0 0, by field_simp⟩
    have hXq : X ^ 2 ^ s * G 0 0 ^ 2 ^ s = G 1 0 ^ 2 ^ s := by rw [← mul_pow, hX]
    have hYq : Y ^ 2 ^ s * G 0 0 ^ 2 ^ s = G 2 0 ^ 2 ^ s := by rw [← mul_pow, hY]
    have hXY : Y + Y ^ 2 ^ s = X * X ^ 2 ^ s := by
      have key : (Y + Y ^ 2 ^ s - X * X ^ 2 ^ s) * (G 0 0 * G 0 0 ^ 2 ^ s) = 0 := by
        linear_combination (G 0 0 ^ 2 ^ s) * hY + G 0 0 * hYq -
          X ^ 2 ^ s * G 0 0 ^ 2 ^ s * hX - G 1 0 * hXq + hiso - G 1 0 ^ 2 ^ s * G 1 0 * h2
      have hne : G 0 0 * G 0 0 ^ 2 ^ s ≠ 0 := mul_ne_zero h00 (pow_ne_zero _ h00)
      linear_combination (mul_eq_zero.mp key).resolve_right hne
    set l : suJ K s := ⟨u3 X Y (X ^ 2 ^ s), u3_mem_suJ hK hXY⟩ with hl
    have hlL : l ∈ LJ K s := mem_lowerUni.mpr ⟨_, _, _, rfl⟩
    have hcoe : ((l⁻¹ * g : suJ K s) : SL(3, K)) =
        u3 X (Y + X * X ^ 2 ^ s) (X ^ 2 ^ s) * (g : SL(3, K)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hl, u3_inv]
    have hent1 : (((l⁻¹ * g : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 0 =
        X * G 0 0 + G 1 0 := by
      rw [hcoe, Matrix.SpecialLinearGroup.coe_mul, u3_coe]
      simp [u3Mat, Matrix.mul_apply, Fin.sum_univ_three, hG]
    have hent2 : (((l⁻¹ * g : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 0 =
        (Y + X * X ^ 2 ^ s) * G 0 0 + X ^ 2 ^ s * G 1 0 + G 2 0 := by
      rw [hcoe, Matrix.SpecialLinearGroup.coe_mul, u3_coe]
      simp [u3Mat, Matrix.mul_apply, Fin.sum_univ_three, hG]
    obtain ⟨h, hh, u, hu, e⟩ := exists_HJ_UJ_of_col hK (g := l⁻¹ * g)
      (by rw [hent1]; linear_combination hX + G 1 0 * h2)
      (by rw [hent2]; linear_combination hY + X ^ 2 ^ s * hX + (G 2 0 + X ^ 2 ^ s * G 1 0) * h2)
    refine ⟨l, hlL, h, hh, u, hu, ?_⟩
    rw [← e, ← mul_assoc, mul_inv_cancel, one_mul]

end CFSG.Quasithin.B45U3
