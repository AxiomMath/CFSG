module

public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.S15223P4.C.Nat4

open Matrix CFSG.Quasithin.FLc CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem mem_QI_one_iff {m : ℕ} {g : SLt (m + 1)} :
    g ∈ QI (m + 1) {1} ↔
      ∀ i : Fin m, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ 0 = 0 := by
  rw [mem_flagStabilizer]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff]
  constructor
  · intro h i
    exact h i.succ 0 (by simp) (by simp)
  · intro h i j hi hj
    have hj0 : j = 0 := Fin.ext (by simpa using hj)
    have hi0 : i ≠ 0 := fun h0 => by subst h0; simp at hi
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi0
    subst hj0
    exact h i'

@[expose] def blk {m : ℕ} (g : SLt (m + 1)) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).submatrix Fin.succ Fin.succ

theorem blk_apply {m : ℕ} (g : SLt (m + 1)) (i j : Fin m) :
    blk g i j = (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ j.succ := rfl

theorem det_eq_mul_det_blk {m : ℕ} {g : SLt (m + 1)} (hg : g ∈ QI (m + 1) {1}) :
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).det =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 0 * (blk g).det := by
  have h1 := mem_QI_one_iff.1 hg
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h1, blk, Fin.succAbove_zero]

theorem det_blk {m : ℕ} {g : SLt (m + 1)} (hg : g ∈ QI (m + 1) {1}) : (blk g).det = 1 := by
  have h := det_eq_mul_det_blk hg
  rw [Matrix.SpecialLinearGroup.det_coe] at h
  generalize (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 0 = a at h
  generalize (blk g).det = b at h ⊢
  revert a b
  decide

theorem blk_mul {m : ℕ} {g : SLt (m + 1)} (hg : g ∈ QI (m + 1) {1}) (h : SLt (m + 1)) :
    blk (g * h) = blk g * blk h := by
  have h1 := mem_QI_one_iff.1 hg
  ext i j
  simp only [blk_apply, Matrix.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
  rw [Fin.sum_univ_succ]
  simp [h1 i]

@[expose] def blkHom (m : ℕ) : ↥(QI (m + 1) {1}) →* SLt m where
  toFun g := ⟨blk g.1, det_blk g.2⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [blk_apply, Matrix.one_apply, Fin.succ_inj]
  map_mul' g h := by
    refine Subtype.ext ?_
    exact blk_mul g.2 h.1

theorem blkHom_coe {m : ℕ} (g : ↥(QI (m + 1) {1})) (i j : Fin m) :
    (blkHom m g : Matrix (Fin m) (Fin m) (ZMod 2)) i j =
      (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ j.succ := rfl

@[expose] def liftMat {m : ℕ} (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of fun i j => Fin.cases (motive := fun _ => ZMod 2)
    (Fin.cases (motive := fun _ => ZMod 2) 1 (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => ZMod 2) 0 (fun j' => B i' j') j) i

@[simp] theorem liftMat_zero_zero {m : ℕ} (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    liftMat B 0 0 = 1 := rfl

@[simp] theorem liftMat_succ_zero {m : ℕ} (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i : Fin m) :
    liftMat B i.succ 0 = 0 := rfl

@[simp] theorem liftMat_succ_succ {m : ℕ} (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i j : Fin m) :
    liftMat B i.succ j.succ = B i j := rfl

theorem det_liftMat {m : ℕ} (B : Matrix (Fin m) (Fin m) (ZMod 2)) : (liftMat B).det = B.det := by
  have hsub : (liftMat B).submatrix Fin.succ Fin.succ = B := by
    ext i j
    simp
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero, hsub]

@[expose] def sec {m : ℕ} (B : SLt m) : ↥(QI (m + 1) {1}) :=
  ⟨⟨liftMat B.1, by rw [det_liftMat]; exact B.2⟩, mem_QI_one_iff.2 fun i => liftMat_succ_zero B.1 i⟩

theorem blkHom_sec {m : ℕ} (B : SLt m) : blkHom m (sec B) = B := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact liftMat_succ_succ B.1 i j

theorem blkHom_surjective (m : ℕ) : Function.Surjective (blkHom m) := fun B =>
  ⟨sec B, blkHom_sec B⟩

theorem mul_self_eq_one_of_blkHom_eq_one {m : ℕ} {g : ↥(QI (m + 1) {1})} (hg : blkHom m g = 1) :
    (g : SLt (m + 1)) * g = 1 := by
  have h1 := mem_QI_one_iff.1 g.2
  have h3 : ∀ i j : Fin m, (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ j.succ =
      (1 : Matrix (Fin m) (Fin m) (ZMod 2)) i j := by
    intro i j
    have := congrArg (fun x : SLt m => (x : Matrix (Fin m) (Fin m) (ZMod 2)) i j) hg
    simpa [blkHom_coe] using this
  have h2 : (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 0 = 1 := by
    have h := det_eq_mul_det_blk g.2
    have hb : blk g.1 = 1 := by
      ext i j
      exact h3 i j
    rw [Matrix.SpecialLinearGroup.det_coe, hb, Matrix.det_one, mul_one] at h
    exact h.symm
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2]
  · have h0 : (0 : Fin (m + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h2, h3, Matrix.one_apply, h0,
      CharTwo.add_self_eq_zero]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h2]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, h1, h3, Matrix.one_apply]

theorem blkHom_mem_Ut {m : ℕ} {g : ↥(QI (m + 1) {1})} (hg : (g : SLt (m + 1)) ∈ Ut (m + 1)) :
    blkHom m g ∈ Ut m := by
  rw [← upperTriangular_eq_Ut] at hg ⊢
  rw [mem_upperTriangular]
  intro i j hij
  exact (mem_upperTriangular.1 hg) i.succ j.succ (Fin.succ_lt_succ_iff.2 hij)

end CFSG.Quasithin.S15223P4.C.Nat4
