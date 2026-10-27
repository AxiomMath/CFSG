module

public import CFSG.RankThree.PartOne.SLB4B.ModelL

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Block

variable {K : Type} [Field K] {m : ℕ}

theorem blockMat_transpose (A : Matrix (Fin 4) (Fin 4) K) :
    (blockMat (m := m) A)ᵀ = blockMat Aᵀ := by
  unfold blockMat
  rw [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

theorem blockMat_map {f : K → K} (h0 : f 0 = 0) (h1 : f 1 = 1) (A : Matrix (Fin 4) (Fin 4) K) :
    (blockMat (m := m) A).map f = blockMat (A.map f) := by
  unfold blockMat
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.reindex_apply,
    ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp [Matrix.map_zero _ h0, Matrix.map_one _ h0 h1]

theorem signMat_transpose : (signMat (F := K) (m := m))ᵀ = signMat := by
  unfold signMat
  rw [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp

theorem signMat_map {f : K → K} (h0 : f 0 = 0) (h1 : f 1 = 1) (hn : f (-1) = -1) :
    (signMat (F := K) (m := m)).map f = signMat := by
  unfold signMat
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, ← Matrix.submatrix_map,
    Matrix.fromBlocks_map]
  have h4 : (-1 : Matrix (Fin 4) (Fin 4) K).map f = -1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp [h0, hn]
  simp [Matrix.map_zero _ h0, Matrix.map_one _ h0 h1, h4]

theorem blockMat_mul_signMat (A : Matrix (Fin 4) (Fin 4) K) :
    blockMat (m := m) A * signMat = signMat * blockMat A := by
  unfold blockMat signMat
  rw [← map_mul, ← map_mul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem signMat_inl_inl (i j : Fin 4) :
    signMat (F := K) (m := m) (Fin.castAdd m i) (Fin.castAdd m j) =
      (-1 : Matrix (Fin 4) (Fin 4) K) i j := by
  simp [signMat]

theorem signMat_inr_inr (i j : Fin m) :
    signMat (F := K) (m := m) (Fin.natAdd 4 i) (Fin.natAdd 4 j) =
      (1 : Matrix (Fin m) (Fin m) K) i j := by
  simp [signMat]

theorem scalar_entry {n : ℕ} (c : Kˣ) (i : Fin n) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i i = (c : K) := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

@[expose] noncomputable def blockGL : GL (Fin 4) K →* GL (Fin (4 + m)) K :=
  Units.map
    { toFun := blockMat
      map_one' := blockMat_one
      map_mul' := blockMat_mul }

theorem coe_blockGL (A : GL (Fin 4) K) :
    ((blockGL (m := m) A : GL (Fin (4 + m)) K) : Matrix (Fin (4 + m)) (Fin (4 + m)) K) =
      blockMat (A : Matrix (Fin 4) (Fin 4) K) :=
  rfl

theorem map_blockGL_statedSU_le {q : ℕ} (hq : 1 ≤ q) :
    (StatedSU 4 q K).map (blockGL (m := m)) ≤ StatedSU (4 + m) q K := by
  rw [StatedSU, MonoidHom.map_closure, StatedSU]
  apply Subgroup.closure_mono
  rintro _ ⟨A, ⟨hdet, hu⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [coe_blockGL, det_blockMat, hdet]
  · rw [coe_blockGL, blockMat_map (f := fun x : K => x ^ q)
      (by simp [Nat.one_le_iff_ne_zero.mp hq]) (by simp), blockMat_transpose, ← blockMat_mul, hu,
      blockMat_one]

@[expose] def signGL : GL (Fin (4 + m)) K :=
  ⟨signMat, signMat, signMat_mul_self, signMat_mul_self⟩

theorem coe_signGL : ((signGL (K := K) (m := m) : GL (Fin (4 + m)) K) :
    Matrix (Fin (4 + m)) (Fin (4 + m)) K) = signMat :=
  rfl

theorem signGL_mem_statedSU {q : ℕ} (hq : Odd q) :
    (signGL : GL (Fin (4 + m)) K) ∈ StatedSU (4 + m) q K := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [coe_signGL]
    exact det_signMat
  · rw [coe_signGL, signMat_map (f := fun x : K => x ^ q) (by simp [hq.pos.ne']) (by simp)
      (by simpa using hq.neg_one_pow), signMat_transpose, signMat_mul_self]

theorem signGL_sq : (signGL : GL (Fin (4 + m)) K) ^ 2 = 1 := by
  apply Units.ext
  rw [pow_two, Units.val_mul, coe_signGL, signMat_mul_self, Units.val_one]

theorem blockGL_commute_signGL (A : GL (Fin 4) K) :
    blockGL (m := m) A * signGL = signGL * blockGL A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blockGL, coe_signGL]
  exact blockMat_mul_signMat _

theorem signGL_not_scalar (hm : 1 ≤ m) (h : (-1 : K) ≠ 1) :
    (signGL : GL (Fin (4 + m)) K) ∉ StatedScalars (Fin (4 + m)) K := by
  rintro ⟨c, hc⟩
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have e1 := congrArg (fun g : GL (Fin (4 + m)) K =>
    Units.val g (Fin.castAdd m (0 : Fin 4)) (Fin.castAdd m (0 : Fin 4))) hc
  have e2 := congrArg (fun g : GL (Fin (4 + m)) K =>
    Units.val g (Fin.natAdd 4 i₀) (Fin.natAdd 4 i₀)) hc
  simp only [scalar_entry, coe_signGL, signMat_inl_inl, signMat_inr_inr] at e1 e2
  simp at e1 e2
  exact h (by simpa using congrArg Units.val (e1.symm.trans e2))

theorem blockGL_eq_one_of_scalar (hm : 1 ≤ m) {A : GL (Fin 4) K}
    (hA : blockGL (m := m) A ∈ StatedScalars (Fin (4 + m)) K) : A = 1 := by
  obtain ⟨c, hc⟩ := hA
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have e2 := congrArg (fun g : GL (Fin (4 + m)) K =>
    Units.val g (Fin.natAdd 4 i₀) (Fin.natAdd 4 i₀)) hc
  simp only [scalar_entry, coe_blockGL, blockMat_inr_inr] at e2
  have hc1 : c = 1 := Units.ext (by simpa using e2)
  rw [hc1, map_one] at hc
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL (Fin (4 + m)) K =>
    Units.val g (Fin.castAdd m i) (Fin.castAdd m j)) hc
  simpa [coe_blockGL, blockMat_inl_inl, Matrix.one_apply] using this.symm

end Block

section PSU

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def suBlock {q : ℕ} (hq : 1 ≤ q) :
    StatedSU 4 q K →* StatedSU (4 + m) q K :=
  ((blockGL (m := m)).comp (StatedSU 4 q K).subtype).codRestrict (StatedSU (4 + m) q K) fun A =>
    map_blockGL_statedSU_le hq ⟨A, A.2, rfl⟩

theorem coe_suBlock {q : ℕ} (hq : 1 ≤ q) (A : StatedSU 4 q K) :
    ((suBlock (m := m) hq A : StatedSU (4 + m) q K) : GL (Fin (4 + m)) K) =
      blockGL (A : GL (Fin 4) K) :=
  rfl

@[expose] def suSign {q : ℕ} (hq : Odd q) : StatedSU (4 + m) q K :=
  ⟨signGL, signGL_mem_statedSU hq⟩

@[expose] noncomputable def psuEmb {q : ℕ} (hq : 1 ≤ q) :
    StatedSU 4 q K →* StatedProj (StatedSU (4 + m) q K) :=
  (QuotientGroup.mk' _).comp (suBlock hq)

theorem psuEmb_injective {q : ℕ} (hq : 1 ≤ q) (hm : 1 ≤ m) :
    Function.Injective (psuEmb (K := K) (m := m) hq) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [psuEmb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hA
  exact Subtype.ext (blockGL_eq_one_of_scalar hm hA)

@[expose] noncomputable def psuSign {q : ℕ} (hq : Odd q) : StatedProj (StatedSU (4 + m) q K) :=
  QuotientGroup.mk' _ (suSign hq)

theorem psuEmb_comm {q : ℕ} (hq : 1 ≤ q) (hq' : Odd q) (A : StatedSU 4 q K) :
    psuEmb (m := m) hq A * psuSign hq' = psuSign hq' * psuEmb hq A := by
  rw [psuEmb, psuSign, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (blockGL_commute_signGL _)

theorem orderOf_psuSign {q : ℕ} (hq : Odd q) (hm : 1 ≤ m) (h : (-1 : K) ≠ 1) :
    orderOf (psuSign (K := K) (m := m) hq) = 2 := by
  have h2 : (psuSign (K := K) (m := m) hq) ^ 2 = 1 := by
    rw [psuSign, ← map_pow, show (suSign (K := K) (m := m) hq) ^ 2 = 1 from
      Subtype.ext signGL_sq, map_one]
  refine orderOf_eq_prime h2 fun h1 => ?_
  rw [psuSign, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact signGL_not_scalar hm h h1

end PSU

end CFSG.RankThree.PartOne.SLB4B
