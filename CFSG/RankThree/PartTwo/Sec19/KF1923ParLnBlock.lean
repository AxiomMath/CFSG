module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.RankThree.PartTwo.Late.KFParLn

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev S2 (m : ℕ) : Type := Matrix.SpecialLinearGroup (Fin m) (ZMod 2)

variable {i j : ℕ}

@[expose] def LL (M : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) : Prop :=
  ∀ (d : Fin j) (c : Fin i), M (Fin.natAdd i d) (Fin.castAdd j c) = 0

@[expose] def blk1 (M : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) :
    Matrix (Fin i) (Fin i) (ZMod 2) :=
  M.submatrix (Fin.castAdd j) (Fin.castAdd j)

@[expose] def blk2 (M : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) :
    Matrix (Fin j) (Fin j) (ZMod 2) :=
  M.submatrix (Fin.natAdd i) (Fin.natAdd i)

theorem blk1_mul (M N : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) (hN : LL N) :
    blk1 (M * N) = blk1 M * blk1 N := by
  have hN' : ∀ (d : Fin j) (c : Fin i), N (Fin.natAdd i d) (Fin.castAdd j c) = 0 := hN
  ext a c
  simp only [blk1, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp [hN']

theorem blk2_mul (M N : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) (hM : LL M) :
    blk2 (M * N) = blk2 M * blk2 N := by
  have hM' : ∀ (d : Fin j) (c : Fin i), M (Fin.natAdd i d) (Fin.castAdd j c) = 0 := hM
  ext d e
  simp only [blk2, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp [hM']

theorem det_eq_blk (M : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) (hM : LL M) :
    M.det = (blk1 M).det * (blk2 M).det := by
  have hM' : ∀ (d : Fin j) (c : Fin i), M (Fin.natAdd i d) (Fin.castAdd j c) = 0 := hM
  have h : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (blk1 M) (M.submatrix (Fin.castAdd j) (Fin.natAdd i)) 0 (blk2 M) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> simp [blk1, blk2, hM']
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, h, Matrix.det_fromBlocks_zero₂₁]

theorem LL_of_mem_stabilizer {g : S2 (i + j)}
    (hg : g ∈ stabilizer (flagSpace (i + j) (ZMod 2) i)) :
    LL (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) := by
  intro d c
  have hv : (Pi.single (Fin.castAdd j c) (1 : ZMod 2) : Fin (i + j) → ZMod 2) ∈
      flagSpace (i + j) (ZMod 2) i := by
    rw [mem_flagSpace]
    intro k hk
    have hne : k ≠ Fin.castAdd j c := fun h => by
      subst h
      exact absurd (by simpa using hk) (not_le.2 c.isLt)
    simp [Pi.single_apply, hne]
  have hmem : (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) *ᵥ
      (Pi.single (Fin.castAdd j c) (1 : ZMod 2)) ∈ flagSpace (i + j) (ZMod 2) i := by
    have h1 := Submodule.mem_map_of_mem
      (f := mulVecLin (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2))) hv
    rwa [mem_stabilizer.1 hg] at h1
  have h2 := (mem_flagSpace.1 hmem) (Fin.natAdd i d) (by simp)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem det_blk1_eq_one {g : S2 (i + j)}
    (hg : LL (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2))) :
    (blk1 (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2))).det = 1 := by
  have h := det_eq_blk _ hg
  rw [g.2] at h
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  exact key _ _ h.symm

theorem det_blk2_eq_one {g : S2 (i + j)}
    (hg : LL (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2))) :
    (blk2 (g : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2))).det = 1 := by
  have h := det_eq_blk _ hg
  rw [g.2] at h
  have key : ∀ x y : ZMod 2, x * y = 1 → y = 1 := by decide
  exact key _ _ h.symm

@[expose] noncomputable def blockHom1 (i j : ℕ) :
    ↥(stabilizer (flagSpace (i + j) (ZMod 2) i)) →* S2 i where
  toFun g := ⟨blk1 (g.1 : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)),
    det_blk1_eq_one (LL_of_mem_stabilizer g.2)⟩
  map_one' := by
    apply Subtype.ext
    simp [blk1, Matrix.submatrix_one _ (Fin.castAdd_injective i j)]
  map_mul' g h := by
    apply Subtype.ext
    exact blk1_mul (g.1 : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) h.1
      (LL_of_mem_stabilizer h.2)

@[expose] noncomputable def blockHom2 (i j : ℕ) :
    ↥(stabilizer (flagSpace (i + j) (ZMod 2) i)) →* S2 j where
  toFun g := ⟨blk2 (g.1 : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)),
    det_blk2_eq_one (LL_of_mem_stabilizer g.2)⟩
  map_one' := by
    apply Subtype.ext
    simp [blk2, Matrix.submatrix_one _ (Fin.natAdd_injective j i)]
  map_mul' g h := by
    apply Subtype.ext
    exact blk2_mul (g.1 : Matrix (Fin (i + j)) (Fin (i + j)) (ZMod 2)) h.1
      (LL_of_mem_stabilizer g.2)

@[simp] theorem blockHom1_coe (g : ↥(stabilizer (flagSpace (i + j) (ZMod 2) i))) :
    ((blockHom1 i j g : S2 i) : Matrix (Fin i) (Fin i) (ZMod 2)) =
      (g : S2 (i + j)).1.submatrix (Fin.castAdd j) (Fin.castAdd j) := rfl

@[simp] theorem blockHom2_coe (g : ↥(stabilizer (flagSpace (i + j) (ZMod 2) i))) :
    ((blockHom2 i j g : S2 j) : Matrix (Fin j) (Fin j) (ZMod 2)) =
      (g : S2 (i + j)).1.submatrix (Fin.natAdd i) (Fin.natAdd i) := rfl

theorem castAdd_ne_natAdd (a : Fin i) (f : Fin j) : Fin.castAdd j a ≠ Fin.natAdd i f := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := a.isLt
  simp at h1
  omega

theorem natAdd_ne_castAdd (a : Fin i) (f : Fin j) : Fin.natAdd i f ≠ Fin.castAdd j a :=
  (castAdd_ne_natAdd a f).symm

@[expose] noncomputable def embed1 (b : S2 i) (j : ℕ) : S2 (i + j) :=
  ⟨(Matrix.fromBlocks b.1 0 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm, by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, b.2, Matrix.det_one,
      one_mul]⟩

@[expose] noncomputable def embed2 (i : ℕ) (b : S2 j) : S2 (i + j) :=
  ⟨(Matrix.fromBlocks 1 0 0 b.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm, by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, b.2, Matrix.det_one,
      one_mul]⟩

theorem embed1_cc (b : S2 i) (a c : Fin i) :
    (embed1 b j).1 (Fin.castAdd j a) (Fin.castAdd j c) = b.1 a c := by
  simp [embed1]

theorem embed1_cn (b : S2 i) (a : Fin i) (d : Fin j) :
    (embed1 b j).1 (Fin.castAdd j a) (Fin.natAdd i d) = 0 := by
  simp [embed1]

theorem embed1_nc (b : S2 i) (a : Fin i) (d : Fin j) :
    (embed1 b j).1 (Fin.natAdd i d) (Fin.castAdd j a) = 0 := by
  simp [embed1]

theorem embed1_nn (b : S2 i) (d e : Fin j) :
    (embed1 b j).1 (Fin.natAdd i d) (Fin.natAdd i e) =
      (1 : Matrix (Fin j) (Fin j) (ZMod 2)) d e := by
  simp [embed1]

theorem embed2_cc (b : S2 j) (a c : Fin i) :
    (embed2 i b).1 (Fin.castAdd j a) (Fin.castAdd j c) =
      (1 : Matrix (Fin i) (Fin i) (ZMod 2)) a c := by
  simp [embed2]

theorem embed2_cn (b : S2 j) (a : Fin i) (d : Fin j) :
    (embed2 i b).1 (Fin.castAdd j a) (Fin.natAdd i d) = 0 := by
  simp [embed2]

theorem embed2_nc (b : S2 j) (a : Fin i) (d : Fin j) :
    (embed2 i b).1 (Fin.natAdd i d) (Fin.castAdd j a) = 0 := by
  simp [embed2]

theorem embed2_nn (b : S2 j) (d e : Fin j) :
    (embed2 i b).1 (Fin.natAdd i d) (Fin.natAdd i e) = b.1 d e := by
  simp [embed2]

theorem embed1_mem_upper {b : S2 i} (hb : b ∈ upperTriangular i (ZMod 2)) :
    embed1 b j ∈ upperTriangular (i + j) (ZMod 2) := by
  intro x y hxy
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left c =>
      have hca : c < a := by
        have h := Fin.lt_def.1 hxy
        simp only [Fin.coe_castAdd] at h
        exact h
      rw [embed1_cc]
      exact hb a c hca
    | right d => exact embed1_cn b a d
  | right d =>
    induction y using Fin.addCases with
    | left c => exact embed1_nc b c d
    | right e =>
      have hed : d ≠ e := by
        have h := Fin.lt_def.1 hxy
        simp only [Fin.coe_natAdd] at h
        have : e < d := by omega
        exact this.ne'
      rw [embed1_nn]
      exact Matrix.one_apply_ne hed

theorem embed2_mem_upper {b : S2 j} (hb : b ∈ upperTriangular j (ZMod 2)) :
    embed2 i b ∈ upperTriangular (i + j) (ZMod 2) := by
  intro x y hxy
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left c =>
      have hca : c ≠ a := by
        have h := Fin.lt_def.1 hxy
        simp only [Fin.coe_castAdd] at h
        have : c < a := by omega
        exact this.ne
      rw [embed2_cc]
      exact Matrix.one_apply_ne hca.symm
    | right d => exact embed2_cn b a d
  | right d =>
    induction y using Fin.addCases with
    | left c => exact embed2_nc b c d
    | right e =>
      have hed : e < d := by
        have h := Fin.lt_def.1 hxy
        simp only [Fin.coe_natAdd] at h
        omega
      rw [embed2_nn]
      exact hb d e hed

theorem exists_block1_upper {b : S2 i} (hb : b ∈ upperTriangular i (ZMod 2)) (j : ℕ) :
    ∃ g : ↥(stabilizer (flagSpace (i + j) (ZMod 2) i)),
      (g : S2 (i + j)) ∈ upperTriangular (i + j) (ZMod 2) ∧ blockHom1 i j g = b := by
  refine ⟨⟨embed1 b j, upperTriangular_le_stabilizer_flagSpace i (embed1_mem_upper hb)⟩,
    embed1_mem_upper hb, ?_⟩
  apply Subtype.ext
  ext a c
  simp [embed1]

theorem exists_block2_upper {b : S2 j} (hb : b ∈ upperTriangular j (ZMod 2)) (i : ℕ) :
    ∃ g : ↥(stabilizer (flagSpace (i + j) (ZMod 2) i)),
      (g : S2 (i + j)) ∈ upperTriangular (i + j) (ZMod 2) ∧ blockHom2 i j g = b := by
  refine ⟨⟨embed2 i b, upperTriangular_le_stabilizer_flagSpace i (embed2_mem_upper hb)⟩,
    embed2_mem_upper hb, ?_⟩
  apply Subtype.ext
  ext a c
  simp [embed2]

theorem sq_eq_one_of_blocks (g : ↥(stabilizer (flagSpace (i + j) (ZMod 2) i)))
    (h1 : blockHom1 i j g = 1) (h2 : blockHom2 i j g = 1) : (g : S2 (i + j)) * g = 1 := by
  have hLL : ∀ (d : Fin j) (c : Fin i),
      (g : S2 (i + j)).1 (Fin.natAdd i d) (Fin.castAdd j c) = 0 := LL_of_mem_stabilizer g.2
  have e1 : ∀ a c, (g : S2 (i + j)).1 (Fin.castAdd j a) (Fin.castAdd j c) =
      (1 : Matrix (Fin i) (Fin i) (ZMod 2)) a c := by
    intro a c
    have := congrArg (fun s : S2 i => (s : Matrix (Fin i) (Fin i) (ZMod 2)) a c) h1
    simpa using this
  have e2 : ∀ d f, (g : S2 (i + j)).1 (Fin.natAdd i d) (Fin.natAdd i f) =
      (1 : Matrix (Fin j) (Fin j) (ZMod 2)) d f := by
    intro d f
    have := congrArg (fun s : S2 j => (s : Matrix (Fin j) (Fin j) (ZMod 2)) d f) h2
    simpa using this
  have two : ∀ x : ZMod 2, x + x = 0 := by decide
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext x y
  induction x using Fin.addCases with
  | left a =>
    induction y using Fin.addCases with
    | left c =>
      rw [Matrix.mul_apply, Fin.sum_univ_add]
      simp [e1, hLL, Matrix.one_apply]
    | right f =>
      rw [Matrix.mul_apply, Fin.sum_univ_add]
      simp [e1, e2, two, Matrix.one_apply, castAdd_ne_natAdd]
  | right d =>
    induction y using Fin.addCases with
    | left c =>
      rw [Matrix.mul_apply, Fin.sum_univ_add]
      simp [e1, hLL, Matrix.one_apply, natAdd_ne_castAdd]
    | right f =>
      rw [Matrix.mul_apply, Fin.sum_univ_add]
      simp [e2, hLL, Matrix.one_apply]

end CFSG.RankThree.PartTwo.Late.KFParLn
