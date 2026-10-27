module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA
public import CFSG.Quasithin.Vol2.KGNatSL3Torus

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def tvec (t : Kˣ × Kˣ) : Fin 3 → K :=
  ![(t.1 : K), (t.2 : K), (((t.1 * t.2)⁻¹ : Kˣ) : K)]

theorem coe_tSL (t : Kˣ × Kˣ) :
    ((tSL t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal (tvec t) :=
  rfl

theorem tvec_ne_zero (t : Kˣ × Kˣ) (i : Fin 3) : tvec t i ≠ 0 := by
  fin_cases i <;> simp [tvec]

theorem tvec_inv (t : Kˣ × Kˣ) (i : Fin 3) : tvec t⁻¹ i = (tvec t i)⁻¹ := by
  fin_cases i <;> simp [tvec, mul_comm]

theorem conj_tSL_apply (t : Kˣ × Kˣ) (B : SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    ((tSL t * B * (tSL t)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      tvec t i * (B : Matrix (Fin 3) (Fin 3) K) i j * (tvec t j)⁻¹ := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tSL,
    coe_tSL, Matrix.mul_diagonal, Matrix.diagonal_mul, tvec_inv]

theorem tSL_mem_stabE0_iff (t : Kˣ × Kˣ) : tSL t ∈ stabE0 K ↔ t.1 = 1 := by
  rw [mem_stabE0, tSL_mulVec]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Matrix.cons_val_zero, mul_one] at h0
    exact Units.ext h0
  · intro h
    rw [h]
    exact KGNat.vec3_eq (by simp) (by simp) (by simp)

theorem tSL_mem_stabRow2_iff (t : Kˣ × Kˣ) : tSL t ∈ stabRow2 K ↔ t.1 * t.2 = 1 := by
  rw [mem_stabRow2, coe_tSL]
  simp only [Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 1 by decide), Matrix.diagonal_apply_eq,
    true_and]
  constructor
  · intro h
    have h' : (((t.1 * t.2)⁻¹ : Kˣ) : K) = 1 := h
    have := Units.ext (h'.trans Units.val_one.symm)
    rwa [inv_eq_one] at this
  · intro h
    simp [tvec, h]

theorem tSL_mulVec_e0 (t : Kˣ × Kˣ) :
    ((tSL t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] =
      (t.1 : K) • ![1, 0, 0] := by
  rw [tSL_mulVec]
  exact KGNat.vec3_eq (by simp) (by simp) (by simp)

theorem conj_tSL_mem_stabE0 (t : Kˣ × Kˣ) {B : SpecialLinearGroup (Fin 3) K}
    (hB : B ∈ stabE0 K) : tSL t * B * (tSL t)⁻¹ ∈ stabE0 K := by
  rw [mem_stabE0] at hB ⊢
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tSL_mulVec_e0, Matrix.mulVec_smul, hB,
    Matrix.mulVec_smul, tSL_mulVec_e0, smul_smul, Prod.fst_inv, Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]

theorem conj_tSL_mem_stabRow2 (t : Kˣ × Kˣ) {B : SpecialLinearGroup (Fin 3) K}
    (hB : B ∈ stabRow2 K) : tSL t * B * (tSL t)⁻¹ ∈ stabRow2 K := by
  obtain ⟨h20, h21, h22⟩ := mem_stabRow2.mp hB
  refine mem_stabRow2.mpr ⟨?_, ?_, ?_⟩ <;> rw [conj_tSL_apply]
  · rw [h20, mul_zero, zero_mul]
  · rw [h21, mul_zero, zero_mul]
  · rw [h22, mul_one, mul_inv_cancel₀ (tvec_ne_zero t 2)]

theorem tSL_mem_normalizer {X : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hX : ∀ s : Kˣ × Kˣ, ∀ B ∈ X, tSL s * B * (tSL s)⁻¹ ∈ X) (t : Kˣ × Kˣ) :
    tSL t ∈ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro B
  refine ⟨hX t B, fun h => ?_⟩
  have := hX t⁻¹ _ h
  rwa [map_inv, inv_inv, show (tSL t)⁻¹ * (tSL t * B * (tSL t)⁻¹) * tSL t = B by group] at this

theorem conj_tSL_mem_rad1 (t : Kˣ × Kˣ) {B : SpecialLinearGroup (Fin 3) K}
    (hB : B ∈ rad1 K) : tSL t * B * (tSL t)⁻¹ ∈ rad1 K := by
  obtain ⟨a, b, rfl⟩ := mem_rad1_iff_uSL.mp hB
  rw [tSL_conj_uSL, mul_zero]
  exact mem_rad1_iff_uSL.mpr ⟨_, _, rfl⟩

theorem conj_tSL_mem_rad2 (t : Kˣ × Kˣ) {B : SpecialLinearGroup (Fin 3) K}
    (hB : B ∈ rad2 K) : tSL t * B * (tSL t)⁻¹ ∈ rad2 K := by
  obtain ⟨b, c, rfl⟩ := mem_rad2_iff_uSL.mp hB
  rw [tSL_conj_uSL, mul_zero]
  exact mem_rad2_iff_uSL.mpr ⟨_, _, rfl⟩

theorem lev_conj_tSL {t : Kˣ × Kˣ} (ht : tvec t 1 = tvec t 2)
    (B : SpecialLinearGroup (Fin 3) K) :
    lev ((tSL t * B * (tSL t)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lev (B : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  rw [lev_apply, lev_apply, conj_tSL_apply]
  have h1 := tvec_ne_zero t 1
  have h2 := tvec_ne_zero t 2
  fin_cases i <;> fin_cases j <;> simp [ht] <;> field_simp

theorem lev2_conj_tSL {t : Kˣ × Kˣ} (ht : tvec t 0 = tvec t 1)
    (B : SpecialLinearGroup (Fin 3) K) :
    lev2 ((tSL t * B * (tSL t)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lev2 (B : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  rw [lev2_apply, lev2_apply, conj_tSL_apply]
  have h1 := tvec_ne_zero t 1
  have h2 := tvec_ne_zero t 2
  fin_cases i <;> fin_cases j <;> simp [ht] <;> field_simp

theorem tSL_mem_sc1_iff (t : Kˣ × Kˣ) :
    tSL t ∈ sectionCentralizer (stabE0 K) (rad1 K) ↔ t.1 * t.2 ^ 2 = 1 := by
  constructor
  · rintro ⟨-, -, h⟩
    have hB0 : uSL (0 : K) 0 1 ∈ stabE0 K := by
      refine mem_stabE0.mpr (KGNat.vec3_eq ?_ ?_ ?_) <;>
        simp [coe_uSL, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have h1 := h _ hB0
    rw [tSL_conj_uSL, uSL_inv, uSL_mul] at h1
    obtain ⟨a, b, hab⟩ := mem_rad1_iff_uSL.mp h1
    have h12 := congrArg
      (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) 1 2) hab
    simp [coe_uSL, uMat] at h12
    apply Units.ext
    push_cast
    linear_combination h12
  · intro ht
    have htv : tvec t 1 = tvec t 2 := by
      have h2 : t.2 = (t.1 * t.2)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by rw [mul_assoc, ← pow_two, ht])
      show ((t.2 : Kˣ) : K) = (((t.1 * t.2)⁻¹ : Kˣ) : K)
      rw [← h2]
    refine ⟨tSL_mem_normalizer (fun s B hB => conj_tSL_mem_stabE0 s hB) t,
      tSL_mem_normalizer (fun s B hB => conj_tSL_mem_rad1 s hB) t, fun B hB => ?_⟩
    have hX := conj_tSL_mem_stabE0 t hB
    have hBi := (stabE0 K).inv_mem hB
    refine mem_rad1.mpr ⟨(stabE0 K).mul_mem hX hBi, ?_⟩
    obtain ⟨-, x10, x20⟩ := stabE0_entries hX
    obtain ⟨-, b10, b20⟩ := stabE0_entries hB
    rw [Matrix.SpecialLinearGroup.coe_mul, lev_mul x10 x20, lev_conj_tSL htv, ← lev_mul b10 b20,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lev]

theorem tSL_mem_sc2_iff (t : Kˣ × Kˣ) :
    tSL t ∈ sectionCentralizer (stabRow2 K) (rad2 K) ↔ t.1 = t.2 := by
  constructor
  · rintro ⟨-, -, h⟩
    have hB0 : uSL (1 : K) 0 0 ∈ stabRow2 K := mem_stabRow2.mpr ⟨rfl, rfl, rfl⟩
    have h1 := h _ hB0
    rw [tSL_conj_uSL, uSL_inv, uSL_mul] at h1
    obtain ⟨b, c, hbc⟩ := mem_rad2_iff_uSL.mp h1
    have h01 := congrArg
      (fun B : SpecialLinearGroup (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K) 0 1) hbc
    simp only [coe_uSL, uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01
    have h2 := Units.ne_zero t.2
    apply Units.ext
    field_simp at h01
    linear_combination h01
  · intro ht
    have htv : tvec t 0 = tvec t 1 := by
      show ((t.1 : Kˣ) : K) = ((t.2 : Kˣ) : K)
      rw [ht]
    refine ⟨tSL_mem_normalizer (fun s B hB => conj_tSL_mem_stabRow2 s hB) t,
      tSL_mem_normalizer (fun s B hB => conj_tSL_mem_rad2 s hB) t, fun B hB => ?_⟩
    have hX := conj_tSL_mem_stabRow2 t hB
    have hBi := (stabRow2 K).inv_mem hB
    refine mem_rad2.mpr ⟨(stabRow2 K).mul_mem hX hBi, ?_⟩
    obtain ⟨c20, c21, -⟩ := mem_stabRow2.mp hBi
    obtain ⟨e20, e21, -⟩ := mem_stabRow2.mp ((stabRow2 K).mul_mem hB hBi)
    rw [Matrix.SpecialLinearGroup.coe_mul, lev2_mul c20 c21, lev2_conj_tSL htv,
      ← lev2_mul c20 c21, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lev2]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
