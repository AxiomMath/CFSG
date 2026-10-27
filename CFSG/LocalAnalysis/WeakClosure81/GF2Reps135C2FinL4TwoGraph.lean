module

public import CFSG.LieType.SpecialLinear.BorelStd
public import CFSG.LargeExtraspecial.SL4ModCodes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LargeExtraspecial.SL4Mod CFSG.LieType.SpecialLinear Matrix
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def graphIdx : ℕ → ℕ
  | 0 => 2
  | 2 => 0
  | 3 => 5
  | 5 => 3
  | n => n

theorem graphIdx_lt {s : ℕ} (hs : s < 6) : graphIdx s < 6 := by
  interval_cases s <;> decide

theorem revGL_mul_self_four : (revGL 4 (ZMod 2) : GL (Fin 4) (ZMod 2)) * revGL 4 (ZMod 2) = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_revGL, Units.val_one]
  decide +kernel

theorem coe_revGL_inv_four :
    (((revGL 4 (ZMod 2))⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      LinearFlag.permMatrix 4 (ZMod 2) Fin.revPerm := by
  rw [inv_eq_of_mul_eq_one_right revGL_mul_self_four, coe_revGL]

theorem borelGraph_genN {s : ℕ} (hs : s < 6) :
    borelGraph 4 (ZMod 2) (genN s) = genN (graphIdx s) := by
  apply Subtype.ext
  rw [coe_borelGraph, genN_inv, coe_revGL_inv_four]
  have h1 := (hasCode_genN s).toMat_eq
  have h2 := (hasCode_genN (graphIdx s)).toMat_eq
  change (genN s : Matrix (Fin 4) (Fin 4) (ZMod 2)) = _ at h1
  change (genN (graphIdx s) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = _ at h2
  rw [h1, h2]
  interval_cases s <;> decide +kernel

theorem borelGraph_wordProd {w : List ℕ} (hw : ∀ s ∈ w, s < 6) :
    borelGraph 4 (ZMod 2) (wordProd w) = wordProd (w.map graphIdx) := by
  induction w with
  | nil => simp [wordProd]
  | cons s w ih =>
    have hs : s < 6 := hw s (List.mem_cons_self ..)
    have hw' : ∀ t ∈ w, t < 6 := fun t ht => hw t (List.mem_cons_of_mem _ ht)
    rw [wordProd_cons, map_mul, borelGraph_genN hs, ih hw', List.map_cons, wordProd_cons]


theorem eq_one_of_isUnit_zmod_two {a : ZMod 2} (h : IsUnit a) : a = 1 := by
  by_contra hne
  have h0 : a = 0 := by
    revert a
    decide
  rw [h0] at h
  exact not_isUnit_zero h

theorem det_gl_eq_one {n : ℕ} (B : GL (Fin n) (ZMod 2)) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
  apply eq_one_of_isUnit_zmod_two
  have h := (Matrix.GeneralLinearGroup.det B).isUnit
  simpa using h

theorem exists_uSL_of_isUpperGL {B : GL (Fin 4) (ZMod 2)} (hB : IsUpperGL B) :
    ∃ k < 64, ((uSL k : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hdet : (B : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 := det_gl_eq_one B
  have hup : (B : Matrix (Fin 4) (Fin 4) (ZMod 2)).BlockTriangular id :=
    fun i j hij => hB i j hij
  have hdiag : ∀ i, (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) i i = 1 := by
    intro i
    have h := Matrix.det_of_upperTriangular hup
    rw [hdet] at h
    have hne : ∏ i, (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) i i ≠ 0 := by
      rw [← h]
      exact one_ne_zero
    have hi := (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
    revert hi
    generalize (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) i i = a
    revert a
    decide
  have hbU : (⟨B.val, hdet⟩ : SL4) ∈ U := ⟨fun i j hji => hB i j hji, hdiag⟩
  obtain ⟨k, hk, hkb⟩ := exists_uSL hbU
  exact ⟨k, hk, by rw [hkb]⟩

theorem coe_sl_inv_eq_gl_inv {R : Type} [CommRing R] {n : ℕ} {B : GL (Fin n) R}
    {b : SpecialLinearGroup (Fin n) R} (hb : (b : Matrix (Fin n) (Fin n) R) = B) :
    ((b⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
  have h1 : ((b⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) * B = 1 := by
    rw [← hb, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 : (B : Matrix (Fin n) (Fin n) R) * ((B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      1 := Units.mul_inv B
  calc ((b⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R)
      = ((b⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) *
          ((B : Matrix (Fin n) (Fin n) R) *
            ((B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) := by
        rw [h2, Matrix.mul_one]
    _ = (((b⁻¹ : SpecialLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) * B) *
          ((B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := (Matrix.mul_assoc _ _ _).symm
    _ = ((B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by rw [h1, Matrix.one_mul]

theorem borelStd_eq_conj {B : GL (Fin 4) (ZMod 2)} {b : SL4}
    (hb : (b : Matrix (Fin 4) (Fin 4) (ZMod 2)) = B) (τ : ZMod 2 ≃+* ZMod 2) (y : SL4) :
    borelStd 4 (ZMod 2) B τ 1 y = b * borelGraph 4 (ZMod 2) y * b⁻¹ := by
  have hτ : ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M.map τ = M := by
    intro M
    ext i j
    rw [Matrix.map_apply]
    have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hbit (M i j) with h | h
    · rw [h, map_zero]
    · rw [h, map_one]
  rw [borelStd_apply, pow_one]
  apply Subtype.ext
  rw [CFSG.QuasithinUnique.K1.coe_stdAut_zero, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hb, hτ, coe_sl_inv_eq_gl_inv hb]

end CFSG.LocalAnalysis.WeakClosure81
