module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open Matrix

section Block

@[expose] def cls : Fin 7 → Fin 3 := ![0, 1, 1, 2, 2, 2, 1]

@[expose] def eV : Fin 3 → Fin 7 := ![2, 1, 6]

theorem eV_injective : Function.Injective eV := by decide

theorem cls_eV (i : Fin 3) : cls (eV i) = 1 := by fin_cases i <;> rfl

theorem exists_eV_of_cls {l : Fin 7} (h : cls l = 1) : ∃ i, eV i = l := by
  fin_cases l <;> simp [cls] at h
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

variable {R : Type*} [CommRing R]

structure IsBD (M : Matrix (Fin 7) (Fin 7) R) : Prop where
  zero : M 0 0 = 1
  off : ∀ k j, cls k ≠ cls j → M k j = 0

theorem IsBD.mul {M N : Matrix (Fin 7) (Fin 7) R} (hM : IsBD M) (hN : IsBD N) :
    IsBD (M * N) where
  zero := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    have : ∀ l : Fin 6, M 0 l.succ * N l.succ 0 = 0 := fun l =>
      by rw [hM.off 0 l.succ (by fin_cases l <;> decide), zero_mul]
    simp [this, hM.zero, hN.zero]
  off k j h := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hkl : cls k = cls l
    · rw [hN.off l j (fun h' => h (hkl.trans h')), mul_zero]
    · rw [hM.off k l hkl, zero_mul]

theorem IsBD.one : IsBD (1 : Matrix (Fin 7) (Fin 7) R) where
  zero := rfl
  off k j h := by
    have : k ≠ j := fun hkj => h (by rw [hkj])
    simp [this]

omit [CommRing R] in
@[expose] def blk (M : Matrix (Fin 7) (Fin 7) R) : Matrix (Fin 3) (Fin 3) R := M.submatrix eV eV

omit [CommRing R] in
theorem blk_apply (M : Matrix (Fin 7) (Fin 7) R) (i j : Fin 3) : blk M i j = M (eV i) (eV j) := rfl

theorem sum_eV {f : Fin 7 → R} (hf : ∀ l, cls l ≠ 1 → f l = 0) :
    ∑ l, f l = ∑ m, f (eV m) := by
  refine (Fintype.sum_of_injective eV eV_injective (fun m => f (eV m)) f ?_ fun _ => rfl).symm
  intro l hl
  refine hf l fun h => hl ?_
  obtain ⟨i, hi⟩ := exists_eV_of_cls h
  exact ⟨i, hi⟩

theorem blk_mul {M N : Matrix (Fin 7) (Fin 7) R} (hN : IsBD N) : blk (M * N) = blk M * blk N := by
  ext i j
  rw [blk_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine sum_eV fun l hl => ?_
  rw [hN.off l (eV j) (by rw [cls_eV]; exact hl), mul_zero]

theorem blk_one : blk (1 : Matrix (Fin 7) (Fin 7) R) = 1 := by
  ext i j
  rw [blk_apply]
  simp [Matrix.one_apply, eV_injective.eq_iff]

theorem mulVec_eV {M : Matrix (Fin 7) (Fin 7) R} (hM : IsBD M) (v : Fin 7 → R) (i : Fin 3) :
    (M *ᵥ v) (eV i) = (blk M *ᵥ fun m => v (eV m)) i := by
  simp only [Matrix.mulVec, dotProduct, blk_apply]
  refine sum_eV fun l hl => ?_
  rw [hM.off (eV i) l (by rw [cls_eV]; exact hl.symm), zero_mul]

theorem mulVec_zero {M : Matrix (Fin 7) (Fin 7) R} (hM : IsBD M) (v : Fin 7 → R) :
    (M *ᵥ v) 0 = v 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ, hM.zero, one_mul]
  have : ∀ l : Fin 6, M 0 l.succ * v l.succ = 0 := fun l => by
    rw [hM.off 0 l.succ (by fin_cases l <;> decide), zero_mul]
  simp [this]

theorem mulVec_w0 {M : Matrix (Fin 7) (Fin 7) R} (hM : IsBD M) :
    M *ᵥ (Pi.single 0 1 : Fin 7 → R) = Pi.single 0 1 := by
  ext k
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hk : k = 0
  · subst hk; simp [hM.zero]
  · rw [hM.off k 0 (by fin_cases k <;> simp_all [cls])]
    simp [hk]

@[expose] def BDGrp (R : Type*) [CommRing R] : Subgroup (GL (Fin 7) R) where
  carrier := {g | IsBD (g : Matrix (Fin 7) (Fin 7) R) ∧ IsBD ((g⁻¹ : GL (Fin 7) R) :
    Matrix (Fin 7) (Fin 7) R)}
  mul_mem' {g h} hg hh := ⟨by rw [Units.val_mul]; exact hg.1.mul hh.1,
    by rw [_root_.mul_inv_rev, Units.val_mul]; exact hh.2.mul hg.2⟩
  one_mem' := ⟨by rw [Units.val_one]; exact IsBD.one,
    by rw [inv_one, Units.val_one]; exact IsBD.one⟩
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem mem_BDGrp {g : GL (Fin 7) R} :
    g ∈ BDGrp R ↔ IsBD (g : Matrix (Fin 7) (Fin 7) R) ∧
      IsBD ((g⁻¹ : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R) := Iff.rfl

@[expose] def blkUnit (g : BDGrp R) : GL (Fin 3) R :=
  ⟨blk (g.1 : Matrix (Fin 7) (Fin 7) R), blk ((g.1⁻¹ : GL (Fin 7) R) : Matrix (Fin 7) (Fin 7) R),
    by rw [← blk_mul g.2.2, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk_one],
    by rw [← blk_mul g.2.1, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk_one]⟩

theorem coe_blkUnit (g : BDGrp R) :
    ((blkUnit g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = blk (g.1 : Matrix (Fin 7) (Fin 7) R) :=
  rfl

@[expose] def blkGL : BDGrp R →* GL (Fin 3) R where
  toFun := blkUnit
  map_one' := by
    refine Units.ext ?_
    rw [coe_blkUnit]
    exact blk_one
  map_mul' g h := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_blkUnit, coe_blkUnit, coe_blkUnit]
    exact blk_mul h.2.1

@[expose] def psi (D : GL (Fin 3) R) : BDGrp R →* GL (Fin 3) R :=
  (MulAut.conj D).toMonoidHom.comp blkGL

theorem coe_psi (D : GL (Fin 3) R) (g : BDGrp R) :
    ((psi D g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (D : Matrix (Fin 3) (Fin 3) R) * blk (g.1 : Matrix (Fin 7) (Fin 7) R) *
        ((D⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  simp [psi, blkGL, blkUnit, Units.val_mul]

theorem isBD_theta0 (M : Matrix (Fin 2) (Fin 2) R) : IsBD (theta0 M) where
  zero := rfl
  off k j h := by
    fin_cases k <;> fin_cases j <;> simp [theta0, cls] at h ⊢

end Block

section Conj

variable {F : Type*} [Field F]

@[expose] def theta2 (y0 : F) (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 7) (Fin 7) F :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, M 0 0, 0, 0, 0, 0, -(M 0 1 * y0 ^ 3);
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, M 1 1, M 1 0 * (y0 ^ 3)⁻¹, 0, 0;
     0, 0, 0, M 0 1 * y0 ^ 3, M 0 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, -(M 1 0 * (y0 ^ 3)⁻¹), 0, 0, 0, 0, M 1 1]

theorem isBD_theta2 (y0 : F) (M : Matrix (Fin 2) (Fin 2) F) : IsBD (theta2 y0 M) where
  zero := rfl
  off k j h := by
    fin_cases k <;> fin_cases j <;> simp [theta2, cls] at h ⊢

set_option maxHeartbeats 1000000 in
theorem theta1_conj {y0 : F} (hy : y0 ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) :
    theta1 !![0, y0; -y0⁻¹, 0] * theta0 M * theta1 !![0, -y0; y0⁻¹, 0] = theta2 y0 M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_seven, theta0, theta1, theta2] <;> field_simp

end Conj

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
