module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

abbrev I6 : Type := Fin 3 ⊕ Fin 3

abbrev W6 (K : Type) [Field K] : Type := StdMod I6 K

@[expose] def tensMat (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix I6 I6 K :=
  Matrix.fromBlocks (M 0 0 • A) (M 0 1 • A) (M 1 0 • A) (M 1 1 • A)

theorem tensMat_mul (A A' : Matrix (Fin 3) (Fin 3) K) (M M' : Matrix (Fin 2) (Fin 2) K) :
    tensMat A M * tensMat A' M' = tensMat (A * A') (M * M') := by
  simp only [tensMat, Matrix.fromBlocks_multiply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← add_smul]
  congr 1 <;> ring_nf

theorem tensMat_one : tensMat (1 : Matrix (Fin 3) (Fin 3) K) 1 = 1 := by
  simp only [tensMat, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), one_smul, zero_smul,
    Matrix.fromBlocks_one]

theorem tensMat_mulVec (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : I6 → K) :
    tensMat A M *ᵥ v = Sum.elim (M 0 0 • (A *ᵥ (v ∘ Sum.inl)) + M 0 1 • (A *ᵥ (v ∘ Sum.inr)))
      (M 1 0 • (A *ᵥ (v ∘ Sum.inl)) + M 1 1 • (A *ᵥ (v ∘ Sum.inr))) := by
  rw [tensMat, Matrix.fromBlocks_mulVec]
  simp only [Matrix.smul_mulVec]

theorem tensMat_mulVec_inl (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : I6 → K) :
    (tensMat A M *ᵥ v) ∘ Sum.inl =
      M 0 0 • (A *ᵥ (v ∘ Sum.inl)) + M 0 1 • (A *ᵥ (v ∘ Sum.inr)) := by
  rw [tensMat_mulVec]
  rfl

theorem tensMat_mulVec_inr (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : I6 → K) :
    (tensMat A M *ᵥ v) ∘ Sum.inr =
      M 1 0 • (A *ᵥ (v ∘ Sum.inl)) + M 1 1 • (A *ᵥ (v ∘ Sum.inr)) := by
  rw [tensMat_mulVec]
  rfl

@[expose] noncomputable def tensHom : GL (Fin 3) K × GL (Fin 2) K →* GL I6 K where
  toFun p :=
    { val := tensMat (p.1 : Matrix (Fin 3) (Fin 3) K) (p.2 : Matrix (Fin 2) (Fin 2) K)
      inv := tensMat ((p.1⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        ((p.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [tensMat_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, mul_inv_cancel,
          Units.val_one, Units.val_one, tensMat_one]
      inv_val := by
        rw [tensMat_mul, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, inv_mul_cancel,
          Units.val_one, Units.val_one, tensMat_one] }
  map_one' := Units.ext (by
    change tensMat ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Units.val_one, Units.val_one, tensMat_one])
  map_mul' p p' := Units.ext (by
    change tensMat (((p.1 * p'.1 : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
      ((p.2 * p'.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      tensMat (p.1 : Matrix (Fin 3) (Fin 3) K) (p.2 : Matrix (Fin 2) (Fin 2) K) *
        tensMat (p'.1 : Matrix (Fin 3) (Fin 3) K) (p'.2 : Matrix (Fin 2) (Fin 2) K)
    rw [tensMat_mul, Units.val_mul, Units.val_mul])

theorem coe_tensHom (A : GL (Fin 3) K) (M : GL (Fin 2) K) :
    ((tensHom (A, M) : GL I6 K) : Matrix I6 I6 K) =
      tensMat (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] noncomputable def dgHom : GL (Fin 3) K →* GL I6 K :=
  tensHom.comp (MonoidHom.inl _ _)

theorem coe_dgHom (g : GL (Fin 3) K) :
    ((dgHom g : GL I6 K) : Matrix I6 I6 K) =
      tensMat (g : Matrix (Fin 3) (Fin 3) K) 1 := by
  change tensMat (g : Matrix (Fin 3) (Fin 3) K) ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [Units.val_one]

theorem dgHom_mulVec_inl (g : GL (Fin 3) K) (v : I6 → K) :
    (((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ v) ∘ Sum.inl =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inl) := by
  rw [coe_dgHom, tensMat_mulVec_inl]
  simp

theorem dgHom_mulVec_inr (g : GL (Fin 3) K) (v : I6 → K) :
    (((dgHom g : GL I6 K) : Matrix I6 I6 K) *ᵥ v) ∘ Sum.inr =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (v ∘ Sum.inr) := by
  rw [coe_dgHom, tensMat_mulVec_inr]
  simp

@[expose] noncomputable def diagSL (K : Type) [Field K] : Subgroup (MulAut (W6 K)) :=
  (StatedSL 3 K).map (matHom.comp dgHom)

theorem matAut_dgHom_mem_diagSL {g : GL (Fin 3) K} (hg : g ∈ StatedSL 3 K) :
    matAut (dgHom g) ∈ diagSL K :=
  ⟨g, hg, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
