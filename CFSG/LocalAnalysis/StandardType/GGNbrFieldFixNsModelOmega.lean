module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

namespace AuxNsDetModel

open Matrix

variable {K : Type} [Field K]

@[expose] def nsEmb {ι : Type*} [DecidableEq ι] (e : Fin 2 × Fin 2 → ι) :
    Matrix ι (Fin 2 × Fin 2) K :=
  fun x a => if x = e a then (1 : K) else 0

lemma nsEmb_apply {ι : Type*} [DecidableEq ι] (e : Fin 2 × Fin 2 → ι) (x : ι)
    (a : Fin 2 × Fin 2) : nsEmb (K := K) e x a = if x = e a then 1 else 0 := rfl

lemma nsEmb_transpose_mul_emb {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) : (nsEmb (K := K) e)ᵀ * nsEmb (K := K) e = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, nsEmb_apply,
    hinj.eq_iff]
  by_cases hab : a = b
  · subst hab; simp
  · have hne : e a ≠ e b := fun h => hab (hinj h)
    simp [hab, hne, Ne.symm hne]

lemma nsEmb_linear {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Fin 2 × Fin 2 → ι)
    (X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) :
    nsEmb (K := K) e * (X + Y) * (nsEmb (K := K) e)ᵀ =
      nsEmb (K := K) e * X * (nsEmb (K := K) e)ᵀ +
        nsEmb (K := K) e * Y * (nsEmb (K := K) e)ᵀ := by
  rw [Matrix.mul_add, Matrix.add_mul]

@[expose] def nsBlk {ι : Type*} [DecidableEq ι] (e : Fin 2 × Fin 2 → ι)
    (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) : Matrix ι ι K :=
  1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ

lemma nsBlk_one {ι : Type*} [DecidableEq ι] (e : Fin 2 × Fin 2 → ι) :
    nsBlk (K := K) e 1 = (1 : Matrix ι ι K) := by
  simp [nsBlk]

lemma nsEmb_conj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) (X Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) :
    nsEmb (K := K) e * X * (nsEmb (K := K) e)ᵀ *
        (nsEmb (K := K) e * Y * (nsEmb (K := K) e)ᵀ) =
      nsEmb (K := K) e * (X * Y) * (nsEmb (K := K) e)ᵀ := by
  rw [show nsEmb (K := K) e * X * (nsEmb (K := K) e)ᵀ *
        (nsEmb (K := K) e * Y * (nsEmb (K := K) e)ᵀ) =
      nsEmb (K := K) e * X * ((nsEmb (K := K) e)ᵀ * nsEmb (K := K) e) * Y *
        (nsEmb (K := K) e)ᵀ from by simp only [Matrix.mul_assoc],
    nsEmb_transpose_mul_emb hinj, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

lemma nsBlk_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) (N N' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) :
    nsBlk (K := K) e N * nsBlk (K := K) e N' = nsBlk (K := K) e (N * N') := by
  have hmid : nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ *
        (nsEmb (K := K) e * (N' - 1) * (nsEmb (K := K) e)ᵀ) =
      nsEmb (K := K) e * ((N - 1) * (N' - 1)) * (nsEmb (K := K) e)ᵀ :=
    nsEmb_conj_mul hinj (N - 1) (N' - 1)
  calc nsBlk (K := K) e N * nsBlk (K := K) e N'
      = (1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ) *
          (1 + nsEmb (K := K) e * (N' - 1) * (nsEmb (K := K) e)ᵀ) := by
        simp only [nsBlk]
    _ = 1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ +
          nsEmb (K := K) e * (N' - 1) * (nsEmb (K := K) e)ᵀ +
          nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ *
            (nsEmb (K := K) e * (N' - 1) * (nsEmb (K := K) e)ᵀ) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
        abel_nf
    _ = 1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ +
          nsEmb (K := K) e * (N' - 1) * (nsEmb (K := K) e)ᵀ +
          nsEmb (K := K) e * ((N - 1) * (N' - 1)) * (nsEmb (K := K) e)ᵀ := by rw [hmid]
    _ = 1 + (nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ +
          nsEmb (K := K) e * (N' - 1) * (nsEmb (K := K) e)ᵀ +
          nsEmb (K := K) e * ((N - 1) * (N' - 1)) * (nsEmb (K := K) e)ᵀ) := by abel
    _ = 1 + nsEmb (K := K) e * ((N - 1) + (N' - 1) + (N - 1) * (N' - 1)) *
          (nsEmb (K := K) e)ᵀ := by
        rw [← nsEmb_linear e (N - 1) (N' - 1),
          ← nsEmb_linear e ((N - 1) + (N' - 1)) ((N - 1) * (N' - 1))]
    _ = 1 + nsEmb (K := K) e * (N * N' - 1) * (nsEmb (K := K) e)ᵀ := by
        congr 2
        noncomm_ring
    _ = nsBlk (K := K) e (N * N') := by simp only [nsBlk]

lemma nsEmb_mul_emb_apply_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : Fin 2 × Fin 2 → ι} (hinj : Function.Injective e)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) (a b : Fin 2 × Fin 2) :
    (nsEmb (K := K) e * M * (nsEmb (K := K) e)ᵀ) (e a) (e b) = M a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, nsEmb_apply, hinj.eq_iff]
  simp

lemma nsEmb_mul_emb_apply_of_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : Fin 2 × Fin 2 → ι} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) {x : ι}
    (hx : x ∉ Set.range e) (y : ι) :
    (nsEmb (K := K) e * M * (nsEmb (K := K) e)ᵀ) x y = 0 := by
  have hx' : ∀ p, x ≠ e p := fun p h => hx ⟨p, h.symm⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, nsEmb_apply]
  simp [hx']

lemma nsBlk_apply_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K)
    (a b : Fin 2 × Fin 2) : nsBlk (K := K) e N (e a) (e b) = N a b := by
  have h1 : (1 : Matrix ι ι K) (e a) (e b) =
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) a b := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (congrArg e hab)]
    · rw [if_neg hab, if_neg (fun h => hab (hinj h))]
  rw [nsBlk, Matrix.add_apply, nsEmb_mul_emb_apply_of_mem hinj (N - 1), Matrix.sub_apply, h1]
  abel

lemma nsBlk_apply_of_not_mem_left {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) {x y : ι} (hx : x ∉ Set.range e) :
    nsBlk (K := K) e N x y = (1 : Matrix ι ι K) x y := by
  rw [nsBlk, Matrix.add_apply, nsEmb_mul_emb_apply_of_not_mem (N - 1) hx, add_zero]

@[expose] def nsReadVec {ι : Type*} (e : Fin 2 × Fin 2 → ι) (v : ι → K) : Fin 2 × Fin 2 → K :=
  fun a => v (e a)

@[expose] def nsReadMat {ι : Type*} (e : Fin 2 × Fin 2 → ι) (v : ι → K) :
    Matrix (Fin 2) (Fin 2) K :=
  fun a b => v (e (a, b))

lemma nsReadMat_apply {ι : Type*} (e : Fin 2 × Fin 2 → ι) (v : ι → K) (a b : Fin 2) :
    nsReadMat e v a b = v (e (a, b)) := rfl

lemma nsEmb_transpose_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Fin 2 × Fin 2 → ι)
    (v : ι → K) : (nsEmb (K := K) e)ᵀ *ᵥ v = nsReadVec e v := by
  ext a
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, nsEmb_apply, nsReadVec]
  simp

lemma nsEmb_mulVec_apply_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) (w : Fin 2 × Fin 2 → K) (a : Fin 2 × Fin 2) :
    (nsEmb (K := K) e *ᵥ w) (e a) = w a := by
  simp only [Matrix.mulVec_apply_eq_sum, nsEmb_apply, hinj.eq_iff]
  simp

lemma nsEmb_mulVec_apply_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Fin 2 × Fin 2 → ι)
    (w : Fin 2 × Fin 2 → K) {x : ι} (hx : x ∉ Set.range e) :
    (nsEmb (K := K) e *ᵥ w) x = 0 := by
  have hx' : ∀ p, x ≠ e p := fun p h => hx ⟨p, h.symm⟩
  simp only [Matrix.mulVec_apply_eq_sum, nsEmb_apply]
  simp [hx']

lemma nsBlk_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Fin 2 × Fin 2 → ι)
    (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) (v : ι → K) :
    nsBlk (K := K) e N *ᵥ v = v + nsEmb (K := K) e *ᵥ ((N - 1) *ᵥ nsReadVec e v) := by
  rw [nsBlk, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nsEmb_transpose_mulVec]

lemma nsBlk_mulVec_apply_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K)
    (v : ι → K) (a : Fin 2 × Fin 2) :
    (nsBlk (K := K) e N *ᵥ v) (e a) = (N *ᵥ nsReadVec e v) a := by
  rw [nsBlk_mulVec_eq, Pi.add_apply, nsEmb_mulVec_apply_mem hinj]
  change nsReadVec e v a + ((N - 1) *ᵥ nsReadVec e v) a = (N *ᵥ nsReadVec e v) a
  rw [show nsReadVec e v a =
      ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) *ᵥ nsReadVec e v) a from by
    rw [Matrix.one_mulVec]]
  rw [← Pi.add_apply, ← Matrix.add_mulVec]
  congr 1
  noncomm_ring

lemma nsBlk_mulVec_apply_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Fin 2 × Fin 2 → ι)
    (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) {x : ι} (hx : x ∉ Set.range e)
    (v : ι → K) : (nsBlk (K := K) e N *ᵥ v) x = v x := by
  rw [nsBlk_mulVec_eq, Pi.add_apply, nsEmb_mulVec_apply_not_mem e _ hx, add_zero]

@[expose] def nsKron (A B : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K :=
  Matrix.kroneckerMap (fun x y : K => x * y) A B

lemma nsKron_apply (A B : Matrix (Fin 2) (Fin 2) K) (p q : Fin 2 × Fin 2) :
    nsKron A B p q = A p.1 q.1 * B p.2 q.2 :=
  Matrix.kronecker_apply A B p.1 p.2 q.1 q.2

lemma nsKron_one_one : nsKron (K := K) 1 1 = 1 := Matrix.one_kronecker_one

lemma nsKron_mul_mul (A B A' B' : Matrix (Fin 2) (Fin 2) K) :
    nsKron (A * B) (A' * B') = nsKron A A' * nsKron B B' :=
  Matrix.mul_kronecker_mul A B A' B'

lemma nsReadMat_nsBlk_nsKron_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : Fin 2 × Fin 2 → ι} (hinj : Function.Injective e) (A : Matrix (Fin 2) (Fin 2) K)
    (v : ι → K) : nsReadMat e (nsBlk (K := K) e (nsKron A 1) *ᵥ v) = A * nsReadMat e v := by
  ext a b
  rw [nsReadMat_apply, nsBlk_mulVec_apply_mem hinj, Matrix.mulVec_apply_eq_sum]
  simp only [Fintype.sum_prod_type, nsKron_apply, Matrix.one_apply, nsReadVec, nsReadMat,
    Matrix.mul_apply]
  simp

lemma nsReadMat_nsBlk_nsKron_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e : Fin 2 × Fin 2 → ι} (hinj : Function.Injective e) (B : Matrix (Fin 2) (Fin 2) K)
    (v : ι → K) : nsReadMat e (nsBlk (K := K) e (nsKron 1 B) *ᵥ v) = nsReadMat e v * Bᵀ := by
  ext a b
  rw [nsReadMat_apply, nsBlk_mulVec_apply_mem hinj, Matrix.mulVec_apply_eq_sum,
    Fintype.sum_prod_type, Finset.sum_comm, Matrix.mul_apply]
  simp [nsKron_apply, Matrix.one_apply, nsReadVec, nsReadMat, Matrix.transpose_apply, mul_comm]

@[expose] def pairEmb {m : ℕ} (i j : Fin m) (p : Fin 2 × Fin 2) : Fin m ⊕ Fin m :=
  !![Sum.inl i, Sum.inl j; Sum.inr j, Sum.inr i] p.1 p.2

lemma pairEmb_zero_zero {m : ℕ} (i j : Fin m) : pairEmb i j (0, 0) = Sum.inl i := by
  simp [pairEmb]

lemma pairEmb_zero_one {m : ℕ} (i j : Fin m) : pairEmb i j (0, 1) = Sum.inl j := by
  simp [pairEmb]

lemma pairEmb_one_zero {m : ℕ} (i j : Fin m) : pairEmb i j (1, 0) = Sum.inr j := by
  simp [pairEmb]

lemma pairEmb_one_one {m : ℕ} (i j : Fin m) : pairEmb i j (1, 1) = Sum.inr i := by
  simp [pairEmb]

lemma pairEmb_injective {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Function.Injective (pairEmb i j) := by
  intro p q h
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [pairEmb, Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, Sum.inl_ne_inr,
      Sum.inr_ne_inl]

lemma inl_notMem_range_pairEmb {m : ℕ} {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Sum.inl k ∉ Set.range (pairEmb i j) := by
  rintro ⟨⟨a, b⟩, hp⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [pairEmb, Sum.inl_injective.eq_iff, Sum.inl_ne_inr, Sum.inr_ne_inl]

lemma inr_notMem_range_pairEmb {m : ℕ} {i j k : Fin m} (hij : i ≠ j) (hkj : k ≠ j) (hki : k ≠ i) :
    Sum.inr k ∉ Set.range (pairEmb i j) := by
  rintro ⟨⟨a, b⟩, hp⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [pairEmb, Sum.inr_injective.eq_iff, Sum.inl_ne_inr, Sum.inr_ne_inl]

lemma pairEmb_range_disjoint {m : ℕ} {i₀ i₁ i₂ i₃ : Fin m}
    (h02 : i₀ ≠ i₂) (h03 : i₀ ≠ i₃) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) :
    Disjoint (Set.range (pairEmb i₀ i₁)) (Set.range (pairEmb i₂ i₃)) := by
  rw [Set.disjoint_left]
  rintro x ⟨⟨a, b⟩, rfl⟩ ⟨⟨c, d⟩, hq⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [pairEmb, Sum.inl_injective.eq_iff, Sum.inr_injective.eq_iff, Sum.inl_ne_inr,
      Sum.inr_ne_inl]

@[expose] def nsRest {m : ℕ} (i j : Fin m) : Finset (Fin m) := (Finset.univ.erase i).erase j

lemma largeEvenQPlus_eq_sum_rest {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (w : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m w =
      (∑ k ∈ nsRest i j, w (Sum.inl k) * w (Sum.inr k)) +
        w (Sum.inl j) * w (Sum.inr j) + w (Sum.inl i) * w (Sum.inr i) := by
  rw [largeEvenQPlus_def]
  dsimp only
  have hj : j ∈ (Finset.univ.erase i : Finset (Fin m)) :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ _ hj]
  rfl

lemma det_fin_two_eq_add [CharP K 2] (M : Matrix (Fin 2) (Fin 2) K) :
    M 0 1 * M 1 0 + M 0 0 * M 1 1 = M.det := by
  rw [Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq]
  ring

lemma nsReadMat_pairEmb_zero_zero {m : ℕ} (i j : Fin m) (v : Fin m ⊕ Fin m → K) :
    nsReadMat (K := K) (pairEmb i j) v 0 0 = v (Sum.inl i) := by
  rw [nsReadMat_apply, pairEmb_zero_zero]

lemma nsReadMat_pairEmb_zero_one {m : ℕ} (i j : Fin m) (v : Fin m ⊕ Fin m → K) :
    nsReadMat (K := K) (pairEmb i j) v 0 1 = v (Sum.inl j) := by
  rw [nsReadMat_apply, pairEmb_zero_one]

lemma nsReadMat_pairEmb_one_zero {m : ℕ} (i j : Fin m) (v : Fin m ⊕ Fin m → K) :
    nsReadMat (K := K) (pairEmb i j) v 1 0 = v (Sum.inr j) := by
  rw [nsReadMat_apply, pairEmb_one_zero]

lemma nsReadMat_pairEmb_one_one {m : ℕ} (i j : Fin m) (v : Fin m ⊕ Fin m → K) :
    nsReadMat (K := K) (pairEmb i j) v 1 1 = v (Sum.inr i) := by
  rw [nsReadMat_apply, pairEmb_one_one]

lemma largeEvenQPlus_nsBlk_eq_of_det [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) (v : Fin m ⊕ Fin m → K)
    (h : (nsReadMat (K := K) (pairEmb i j) (nsBlk (K := K) (pairEmb i j) N *ᵥ v)).det =
      (nsReadMat (K := K) (pairEmb i j) v).det) :
    LargeEvenQPlus K m (nsBlk (K := K) (pairEmb i j) N *ᵥ v) = LargeEvenQPlus K m v := by
  rw [largeEvenQPlus_eq_sum_rest hij, largeEvenQPlus_eq_sum_rest hij]
  have hrest : (∑ k ∈ nsRest i j, (nsBlk (K := K) (pairEmb i j) N *ᵥ v) (Sum.inl k) *
        (nsBlk (K := K) (pairEmb i j) N *ᵥ v) (Sum.inr k)) =
      ∑ k ∈ nsRest i j, v (Sum.inl k) * v (Sum.inr k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    rw [nsBlk_mulVec_apply_not_mem (pairEmb i j) N
        (inl_notMem_range_pairEmb hij hki hkj),
      nsBlk_mulVec_apply_not_mem (pairEmb i j) N
        (inr_notMem_range_pairEmb hij hkj hki)]
  have hspec : (nsBlk (K := K) (pairEmb i j) N *ᵥ v) (Sum.inl j) *
        (nsBlk (K := K) (pairEmb i j) N *ᵥ v) (Sum.inr j) +
        (nsBlk (K := K) (pairEmb i j) N *ᵥ v) (Sum.inl i) *
        (nsBlk (K := K) (pairEmb i j) N *ᵥ v) (Sum.inr i) =
      v (Sum.inl j) * v (Sum.inr j) + v (Sum.inl i) * v (Sum.inr i) := by
    rw [← nsReadMat_pairEmb_zero_one i j (nsBlk (K := K) (pairEmb i j) N *ᵥ v),
      ← nsReadMat_pairEmb_one_zero i j (nsBlk (K := K) (pairEmb i j) N *ᵥ v),
      ← nsReadMat_pairEmb_zero_zero i j (nsBlk (K := K) (pairEmb i j) N *ᵥ v),
      ← nsReadMat_pairEmb_one_one i j (nsBlk (K := K) (pairEmb i j) N *ᵥ v),
      ← nsReadMat_pairEmb_zero_one i j v, ← nsReadMat_pairEmb_one_zero i j v,
      ← nsReadMat_pairEmb_zero_zero i j v, ← nsReadMat_pairEmb_one_one i j v,
      det_fin_two_eq_add (nsReadMat (K := K) (pairEmb i j)
        (nsBlk (K := K) (pairEmb i j) N *ᵥ v)),
      det_fin_two_eq_add (nsReadMat (K := K) (pairEmb i j) v), h]
  rw [hrest, add_assoc, hspec, add_assoc]

lemma largeEvenQPlus_nsBlk_kron_left [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m
        (nsBlk (K := K) (pairEmb i j) (nsKron (A : Matrix (Fin 2) (Fin 2) K) 1) *ᵥ v) =
      LargeEvenQPlus K m v := by
  refine largeEvenQPlus_nsBlk_eq_of_det hij _ v ?_
  rw [nsReadMat_nsBlk_nsKron_left (pairEmb_injective i j hij) (A : Matrix (Fin 2) (Fin 2) K) v,
    Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]

lemma largeEvenQPlus_nsBlk_kron_right [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (B : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m
        (nsBlk (K := K) (pairEmb i j) (nsKron 1 (B : Matrix (Fin 2) (Fin 2) K)) *ᵥ v) =
      LargeEvenQPlus K m v := by
  refine largeEvenQPlus_nsBlk_eq_of_det hij _ v ?_
  rw [nsReadMat_nsBlk_nsKron_right (pairEmb_injective i j hij) (B : Matrix (Fin 2) (Fin 2) K) v,
    Matrix.det_mul, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe, mul_one]

lemma nsEmb_transpose_mul_emb_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e e' : Fin 2 × Fin 2 → ι} (hdisj : Disjoint (Set.range e) (Set.range e')) :
    (nsEmb (K := K) e)ᵀ * nsEmb (K := K) e' = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  rw [show (∑ x, (nsEmb (K := K) e)ᵀ a x * nsEmb (K := K) e' x b) = ∑ _x, (0 : K) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = e a
    · have hxb : x ∉ Set.range e' := (Set.disjoint_left.mp hdisj) ⟨a, hx.symm⟩
      have hne : x ≠ e' b := fun h => hxb ⟨b, h.symm⟩
      simp only [Matrix.transpose_apply, nsEmb_apply, if_pos hx, if_neg hne, mul_zero]
    · simp only [Matrix.transpose_apply, nsEmb_apply, if_neg hx, zero_mul]]
  simp

lemma nsBlk_mul_nsBlk_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e e' : Fin 2 × Fin 2 → ι} (hdisj : Disjoint (Set.range e) (Set.range e'))
    (N N' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) :
    nsBlk (K := K) e N * nsBlk (K := K) e' N' =
      1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ +
        nsEmb (K := K) e' * (N' - 1) * (nsEmb (K := K) e')ᵀ := by
  have hzero : (nsEmb (K := K) e)ᵀ * nsEmb (K := K) e' = 0 :=
    nsEmb_transpose_mul_emb_eq_zero hdisj
  have hcross : nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ *
        (nsEmb (K := K) e' * (N' - 1) * (nsEmb (K := K) e')ᵀ) = 0 := by
    rw [show nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ *
          (nsEmb (K := K) e' * (N' - 1) * (nsEmb (K := K) e')ᵀ) =
        nsEmb (K := K) e * (N - 1) * ((nsEmb (K := K) e)ᵀ * nsEmb (K := K) e') *
          (N' - 1) * (nsEmb (K := K) e')ᵀ from by simp only [Matrix.mul_assoc],
      hzero]
    simp
  rw [nsBlk, nsBlk]
  rw [show (1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ) *
        (1 + nsEmb (K := K) e' * (N' - 1) * (nsEmb (K := K) e')ᵀ) =
      1 + nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ +
        nsEmb (K := K) e' * (N' - 1) * (nsEmb (K := K) e')ᵀ +
        (nsEmb (K := K) e * (N - 1) * (nsEmb (K := K) e)ᵀ *
          (nsEmb (K := K) e' * (N' - 1) * (nsEmb (K := K) e')ᵀ)) from by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    abel_nf]
  rw [hcross, add_zero]

@[expose] noncomputable def nsBlkGL {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) (N : GL (Fin 2 × Fin 2) K) : GL ι K where
  val := nsBlk (K := K) e ↑N
  inv := nsBlk (K := K) e ↑N⁻¹
  val_inv := by
    rw [nsBlk_mul hinj]
    change nsBlk (K := K) e ((N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) * N.inv) = 1
    rw [N.val_inv, nsBlk_one]
  inv_val := by
    rw [nsBlk_mul hinj]
    change nsBlk (K := K) e (N.inv * (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K)) = 1
    rw [N.inv_val, nsBlk_one]

@[expose] noncomputable def nsBlkHom {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Fin 2 × Fin 2 → ι}
    (hinj : Function.Injective e) : GL (Fin 2 × Fin 2) K →* GL ι K where
  toFun := nsBlkGL hinj
  map_one' := Units.ext (nsBlk_one e)
  map_mul' N N' := Units.ext (by
    show nsBlk (K := K) e ↑(N * N') = nsBlk (K := K) e ↑N * nsBlk (K := K) e ↑N'
    rw [Units.val_mul, nsBlk_mul hinj])

lemma nsBlkHom_commute_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {e e' : Fin 2 × Fin 2 → ι} (hinj : Function.Injective e) (hinj' : Function.Injective e')
    (hdisj : Disjoint (Set.range e) (Set.range e'))
    (N N' : GL (Fin 2 × Fin 2) K) :
    Commute (nsBlkHom hinj N) (nsBlkHom hinj' N') := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show nsBlk (K := K) e ↑N * nsBlk (K := K) e' ↑N' =
    nsBlk (K := K) e' ↑N' * nsBlk (K := K) e ↑N
  rw [nsBlk_mul_nsBlk_of_disjoint hdisj, nsBlk_mul_nsBlk_of_disjoint hdisj.symm]
  abel

@[expose] noncomputable def nsKronLeftUnit (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    GL (Fin 2 × Fin 2) K where
  val := nsKron (A : Matrix (Fin 2) (Fin 2) K) 1
  inv := nsKron (↑A⁻¹ : Matrix (Fin 2) (Fin 2) K) 1
  val_inv := by
    rw [← nsKron_mul_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul, nsKron_one_one]
  inv_val := by
    rw [← nsKron_mul_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul, nsKron_one_one]

@[expose] noncomputable def nsKronRightUnit (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    GL (Fin 2 × Fin 2) K where
  val := nsKron 1 (B : Matrix (Fin 2) (Fin 2) K)
  inv := nsKron 1 (↑B⁻¹ : Matrix (Fin 2) (Fin 2) K)
  val_inv := by
    rw [← nsKron_mul_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul, nsKron_one_one]
  inv_val := by
    rw [← nsKron_mul_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul, nsKron_one_one]

lemma nsKronLeftUnit_commute (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (nsKronLeftUnit A) (nsKronRightUnit B) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show nsKron (A : Matrix (Fin 2) (Fin 2) K) 1 * nsKron 1 (B : Matrix (Fin 2) (Fin 2) K) =
    nsKron 1 (B : Matrix (Fin 2) (Fin 2) K) * nsKron (A : Matrix (Fin 2) (Fin 2) K) 1
  rw [← nsKron_mul_mul, ← nsKron_mul_mul]
  simp

@[expose] noncomputable def nsKronLeftHom :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2 × Fin 2) K where
  toFun := nsKronLeftUnit
  map_one' := Units.ext (by simp [nsKronLeftUnit, Matrix.SpecialLinearGroup.coe_one,
    nsKron_one_one])
  map_mul' A B := Units.ext (by
    show nsKron (K := K) (↑(A * B) : Matrix (Fin 2) (Fin 2) K) 1 =
      nsKron (↑A : Matrix (Fin 2) (Fin 2) K) 1 * nsKron (↑B : Matrix (Fin 2) (Fin 2) K) 1
    rw [Matrix.SpecialLinearGroup.coe_mul, ← nsKron_mul_mul]
    simp)

@[expose] noncomputable def nsKronRightHom :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2 × Fin 2) K where
  toFun := nsKronRightUnit
  map_one' := Units.ext (by simp [nsKronRightUnit, Matrix.SpecialLinearGroup.coe_one,
    nsKron_one_one])
  map_mul' A B := Units.ext (by
    show nsKron 1 (↑(A * B) : Matrix (Fin 2) (Fin 2) K) =
      nsKron 1 (↑A : Matrix (Fin 2) (Fin 2) K) * nsKron 1 (↑B : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← nsKron_mul_mul]
    simp)

@[expose] noncomputable def nsLhom {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin m ⊕ Fin m) K :=
  (nsBlkHom (pairEmb_injective i j hij)).comp nsKronLeftHom

@[expose] noncomputable def nsRhom {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin m ⊕ Fin m) K :=
  (nsBlkHom (pairEmb_injective i j hij)).comp nsKronRightHom

lemma coe_nsLhom {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((nsLhom i j hij A : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      nsBlk (K := K) (pairEmb i j) (nsKron (A : Matrix (Fin 2) (Fin 2) K) 1) := rfl

lemma coe_nsRhom {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((nsRhom i j hij B : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      nsBlk (K := K) (pairEmb i j) (nsKron 1 (B : Matrix (Fin 2) (Fin 2) K)) := rfl

lemma nsLhom_mem_orth [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    nsLhom i j hij A ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) := by
  refine mem_orthGroup_of_isometry fun v => ?_
  rw [coe_nsLhom]
  exact largeEvenQPlus_nsBlk_kron_left hij A v

lemma nsRhom_mem_orth [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    nsRhom i j hij B ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) := by
  refine mem_orthGroup_of_isometry fun v => ?_
  rw [coe_nsRhom]
  exact largeEvenQPlus_nsBlk_kron_right hij B v

lemma le_omega_of_le_orth {m : ℕ} {H : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hH : H ≤ LargeEvenOrthGroup (LargeEvenQPlus K m))
    [Group.IsPerfect H] : H ≤ LargeEvenOmega (LargeEvenQPlus K m) := by
  rw [largeEvenOmega_def]
  intro x hx
  have hx' : x ∈ ⁅H, H⁆ := by rwa [Subgroup.commutator_eq_self]
  exact Subgroup.commutator_mono hH hH hx'

lemma nsLhom_range_le_omega [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    [Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K)] :
    (nsLhom i j hij).range ≤ LargeEvenOmega (LargeEvenQPlus K m) := by
  haveI : Group.IsPerfect (nsLhom (K := K) i j hij).range :=
    Group.IsPerfect.range (nsLhom (K := K) i j hij)
  exact le_omega_of_le_orth (by rintro _ ⟨A, rfl⟩; exact nsLhom_mem_orth hij A)

lemma nsRhom_range_le_omega [CharP K 2] {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    [Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K)] :
    (nsRhom i j hij).range ≤ LargeEvenOmega (LargeEvenQPlus K m) := by
  haveI : Group.IsPerfect (nsRhom (K := K) i j hij).range :=
    Group.IsPerfect.range (nsRhom (K := K) i j hij)
  exact le_omega_of_le_orth (by rintro _ ⟨B, rfl⟩; exact nsRhom_mem_orth hij B)

lemma nsKron_eq_one [CharP K 2] {A B : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1)
    (h : nsKron A B = 1) : A = 1 ∧ B = 1 := by
  have h00 : A 0 0 * B 0 0 = 1 := by
    have := congrFun (congrFun h (0, 0)) (0, 0)
    simpa [nsKron_apply, Matrix.one_apply] using this
  have h11 : A 1 1 * B 0 0 = 1 := by
    have := congrFun (congrFun h (1, 0)) (1, 0)
    simpa [nsKron_apply, Matrix.one_apply] using this
  have h01 : A 0 1 * B 0 0 = 0 := by
    have := congrFun (congrFun h (0, 0)) (1, 0)
    simpa [nsKron_apply, Matrix.one_apply] using this
  have h10 : A 1 0 * B 0 0 = 0 := by
    have := congrFun (congrFun h (1, 0)) (0, 0)
    simpa [nsKron_apply, Matrix.one_apply] using this
  have hB00 : B 0 0 ≠ 0 := fun hB => by
    rw [hB, mul_zero] at h00
    exact one_ne_zero h00.symm
  have hA00 : A 0 0 = A 1 1 := mul_right_cancel₀ hB00 (by rw [h00, h11])
  have hA01 : A 0 1 = 0 := (mul_eq_zero.mp h01).resolve_right hB00
  have hA10 : A 1 0 = 0 := (mul_eq_zero.mp h10).resolve_right hB00
  have hsq : A 0 0 ^ 2 = 1 := by
    have hdet : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
    rw [hA, hA00, hA01, hA10] at hdet
    rw [pow_two, hA00]
    simpa using hdet.symm
  have hA00one : A 0 0 = 1 := by
    rcases (sq_eq_one_iff.mp hsq) with h' | h'
    · exact h'
    · rw [h']; exact CharTwo.neg_eq 1
  have hA1 : A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.one_apply] using hA00one
    · simpa [Matrix.one_apply, hA01]
    · simpa [Matrix.one_apply, hA10]
    · simpa [Matrix.one_apply, ← hA00] using hA00one
  refine ⟨hA1, ?_⟩
  have hB : nsKron (K := K) (1 : Matrix (Fin 2) (Fin 2) K) B = 1 := by
    simpa only [hA1] using h
  ext i j
  have := congrFun (congrFun hB (0, i)) (0, j)
  simpa [nsKron_apply, Matrix.one_apply] using this

lemma nsBlk_mul_nsBlk_apply_of_not_mem_left {m : ℕ} {i₀ i₁ i₂ i₃ : Fin m}
    (h23 : i₂ ≠ i₃)
    (hdisj : Disjoint (Set.range (pairEmb i₀ i₁)) (Set.range (pairEmb i₂ i₃)))
    (M M' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) (p q : Fin 2 × Fin 2) :
    (nsBlk (K := K) (pairEmb i₀ i₁) M * nsBlk (K := K) (pairEmb i₂ i₃) M')
        (pairEmb i₂ i₃ p) (pairEmb i₂ i₃ q) = M' p q := by
  have hmem : pairEmb i₂ i₃ p ∉ Set.range (pairEmb i₀ i₁) :=
    fun h => (Set.disjoint_left.mp hdisj) h ⟨p, rfl⟩
  rw [Matrix.mul_apply]
  rw [show (∑ z, nsBlk (K := K) (pairEmb i₀ i₁) M (pairEmb i₂ i₃ p) z *
        nsBlk (K := K) (pairEmb i₂ i₃) M' z (pairEmb i₂ i₃ q)) =
      ∑ z, (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (pairEmb i₂ i₃ p) z *
        nsBlk (K := K) (pairEmb i₂ i₃) M' z (pairEmb i₂ i₃ q) from by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [nsBlk_apply_of_not_mem_left M hmem]]
  rw [show (∑ z, (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (pairEmb i₂ i₃ p) z *
        nsBlk (K := K) (pairEmb i₂ i₃) M' z (pairEmb i₂ i₃ q)) =
      nsBlk (K := K) (pairEmb i₂ i₃) M' (pairEmb i₂ i₃ p) (pairEmb i₂ i₃ q) from by
    simp [Matrix.one_apply, Finset.sum_ite_eq]]
  exact nsBlk_apply_of_mem (pairEmb_injective i₂ i₃ h23) M' p q

@[expose] noncomputable def nsRootEl (t : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

lemma nsRootEl_zero : nsRootEl (K := K) 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsRootEl]

lemma nsRootEl_add (a b : K) : nsRootEl (K := K) (a + b) = nsRootEl a * nsRootEl b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsRootEl, Matrix.mul_fin_two, add_comm]

@[expose] noncomputable def nsRootHom :
    Multiplicative K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun c := nsRootEl (Multiplicative.toAdd c)
  map_one' := nsRootEl_zero
  map_mul' c d := nsRootEl_add (Multiplicative.toAdd c) (Multiplicative.toAdd d)

lemma nsKron_eq_one_right [CharP K 2] {B : Matrix (Fin 2) (Fin 2) K} (h : nsKron 1 B = 1) :
    B = 1 :=
  (nsKron_eq_one (A := 1) (by simp) h).2

end AuxNsDetModel

open AuxNsDetModel

variable {K : Type} [Field K] {m : ℕ}

theorem exists_nsDetModel [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hm : 4 ≤ m) :
    ∃ (Φ : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin m ⊕ Fin m) K)
      (Y : Multiplicative K →* GL (Fin m ⊕ Fin m) K),
      Function.Injective Φ ∧ (∀ a, Φ a ∈ LargeEvenOmega (LargeEvenQPlus K m)) ∧
      (∀ c, Y c ∈ LargeEvenOmega (LargeEvenQPlus K m)) ∧
      Y (Multiplicative.ofAdd 1) ∉ LargeEvenScalars (Fin m ⊕ Fin m) K ∧
      (∀ c, Y c ^ 2 = 1) ∧ (∀ a c, Φ a * Y c = Y c * Φ a) := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  let i3 : Fin m := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have hv : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
    simp only [i0, i1] at hv
    exact absurd hv (by omega)
  have h02 : i0 ≠ i2 := by
    intro h
    have hv : (i0 : ℕ) = (i2 : ℕ) := congrArg Fin.val h
    simp only [i0, i2] at hv
    exact absurd hv (by omega)
  have h03 : i0 ≠ i3 := by
    intro h
    have hv : (i0 : ℕ) = (i3 : ℕ) := congrArg Fin.val h
    simp only [i0, i3] at hv
    exact absurd hv (by omega)
  have h12 : i1 ≠ i2 := by
    intro h
    have hv : (i1 : ℕ) = (i2 : ℕ) := congrArg Fin.val h
    simp only [i1, i2] at hv
    exact absurd hv (by omega)
  have h13 : i1 ≠ i3 := by
    intro h
    have hv : (i1 : ℕ) = (i3 : ℕ) := congrArg Fin.val h
    simp only [i1, i3] at hv
    exact absurd hv (by omega)
  have h23 : i2 ≠ i3 := by
    intro h
    have hv : (i2 : ℕ) = (i3 : ℕ) := congrArg Fin.val h
    simp only [i2, i3] at hv
    exact absurd hv (by omega)
  have hinj01 : Function.Injective (pairEmb i0 i1) := pairEmb_injective i0 i1 h01
  have hinj23 : Function.Injective (pairEmb i2 i3) := pairEmb_injective i2 i3 h23
  have hdisj : Disjoint (Set.range (pairEmb i0 i1)) (Set.range (pairEmb i2 i3)) :=
    pairEmb_range_disjoint h02 h03 h12 h13
  haveI hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalInvolution.sl2_isPerfect hK
  let L : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin m ⊕ Fin m) K := nsLhom i0 i1 h01
  let R : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin m ⊕ Fin m) K := nsRhom i0 i1 h01
  let R' : Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin m ⊕ Fin m) K := nsRhom i2 i3 h23
  have hLR : ∀ x y, Commute (L x) (R y) := fun x y =>
    (nsKronLeftUnit_commute x y).map (nsBlkHom hinj01)
  have hLR' : ∀ x y, Commute (L x) (R' y) := fun x y =>
    nsBlkHom_commute_of_disjoint hinj01 hinj23 hdisj (nsKronLeftUnit x) (nsKronRightUnit y)
  have hRR' : ∀ x y, Commute (R x) (R' y) := fun x y =>
    nsBlkHom_commute_of_disjoint hinj01 hinj23 hdisj (nsKronRightUnit x) (nsKronRightUnit y)
  let phi : Fin 3 → (Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin m ⊕ Fin m) K) :=
    Fin.cases L (Fin.cases R (fun _ => R'))
  have phi_zero : phi 0 = L := rfl
  have phi_one : phi 1 = R := rfl
  have phi_two : phi 2 = R' := rfl
  have hcommPhi : Pairwise fun i j : Fin 3 => ∀ x y, Commute (phi i x) (phi j y) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hLR
    · exact hLR'
    · exact fun x y => (hLR y x).symm
    · exact absurd rfl hij
    · exact hRR'
    · exact fun x y => (hLR' y x).symm
    · exact fun x y => (hRR' y x).symm
    · exact absurd rfl hij
  let Phi : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin m ⊕ Fin m) K :=
    MonoidHom.noncommPiCoprod phi hcommPhi
  have hPhi_apply : ∀ a, Phi a = L (a 0) * R (a 1) * R' (a 2) := by
    intro a
    have hdecomp : a = Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) * Pi.mulSingle 2 (a 2) := by
      funext k
      fin_cases k <;> simp [Pi.mulSingle]
    rw [hdecomp, map_mul, map_mul, MonoidHom.noncommPiCoprod_mulSingle,
      MonoidHom.noncommPiCoprod_mulSingle, MonoidHom.noncommPiCoprod_mulSingle]
    simp [phi_zero, phi_one, phi_two]
  have hPhiO : ∀ a, Phi a ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
    intro a
    rw [hPhi_apply a]
    exact mul_mem (mul_mem (nsLhom_range_le_omega h01 ⟨a 0, rfl⟩)
      (nsRhom_range_le_omega h01 ⟨a 1, rfl⟩)) (nsRhom_range_le_omega h23 ⟨a 2, rfl⟩)
  let Y : Multiplicative K →* GL (Fin m ⊕ Fin m) K := (nsLhom i2 i3 h23).comp nsRootHom
  have hYO : ∀ c, Y c ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
    intro c
    exact nsLhom_range_le_omega h23 ⟨nsRootHom c, rfl⟩
  have hY2 : ∀ c, Y c ^ 2 = 1 := by
    intro c
    rw [sq, ← map_mul]
    change (nsLhom i2 i3 h23) (nsRootHom (c * c)) = 1
    rw [show nsRootHom (c * c) = 1 from by
      rw [map_mul]
      change nsRootEl (Multiplicative.toAdd c) * nsRootEl (Multiplicative.toAdd c) = 1
      rw [← nsRootEl_add, CharTwo.add_self_eq_zero, nsRootEl_zero], map_one]
  have hY1 : Y (Multiplicative.ofAdd 1) ∉ LargeEvenScalars (Fin m ⊕ Fin m) K := by
    rw [largeEvenScalars_def]
    rintro ⟨u, hu⟩
    have hxy : pairEmb i2 i3 (0, 1) ≠ pairEmb i2 i3 (1, 1) :=
      fun h => (by decide : ((0, 1) : Fin 2 × Fin 2) ≠ (1, 1)) (hinj23 h)
    have hentry := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (pairEmb i2 i3 (0, 1))
        (pairEmb i2 i3 (1, 1))) hu
    rw [show ((Y (Multiplicative.ofAdd 1) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        nsBlk (K := K) (pairEmb i2 i3)
          (nsKron (↑(nsRootEl (1 : K)) : Matrix (Fin 2) (Fin 2) K) 1) from rfl,
      nsBlk_apply_of_mem hinj23] at hentry
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, hxy,
      nsKron_apply, nsRootEl, Matrix.one_apply] at hentry
  have hkron : ∀ a, Phi a = 1 →
      nsKron (K := K) (↑(a 0) : Matrix (Fin 2) (Fin 2) K)
        (↑(a 1) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    intro a ha
    have ha2 : a 2 = 1 := by
      have h23' : nsKron (K := K) 1 (↑(a 2) : Matrix (Fin 2) (Fin 2) K) = 1 := by
        ext p q
        have hentry := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
          (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (pairEmb i2 i3 p)
            (pairEmb i2 i3 q)) ha
        rw [hPhi_apply a] at hentry
        rw [show ((L (a 0) * R (a 1) * R' (a 2) : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
            nsBlk (K := K) (pairEmb i0 i1)
              (nsKron (↑(a 0) : Matrix (Fin 2) (Fin 2) K) (↑(a 1) : Matrix (Fin 2) (Fin 2) K)) *
              nsBlk (K := K) (pairEmb i2 i3) (nsKron 1 (↑(a 2) : Matrix (Fin 2) (Fin 2) K))
            from by
          rw [Units.val_mul, Units.val_mul, coe_nsLhom, coe_nsRhom, coe_nsRhom,
            nsBlk_mul hinj01, ← nsKron_mul_mul]
          simp [Matrix.mul_one, Matrix.one_mul]] at hentry
        rw [nsBlk_mul_nsBlk_apply_of_not_mem_left h23 hdisj] at hentry
        simpa only [Units.val_one, Matrix.one_apply, hinj23.eq_iff] using hentry
      exact Subtype.ext (nsKron_eq_one_right h23')
    ext p q
    have hentry := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (pairEmb i0 i1 p)
        (pairEmb i0 i1 q)) ha
    rw [hPhi_apply a, show R' (a 2) = 1 from by rw [ha2, map_one], mul_one] at hentry
    rw [show ((L (a 0) * R (a 1) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        nsBlk (K := K) (pairEmb i0 i1)
          (nsKron (↑(a 0) : Matrix (Fin 2) (Fin 2) K) (↑(a 1) : Matrix (Fin 2) (Fin 2) K))
        from by
      rw [Units.val_mul, coe_nsLhom, coe_nsRhom, nsBlk_mul hinj01, ← nsKron_mul_mul]
      simp [Matrix.mul_one, Matrix.one_mul]] at hentry
    rw [nsBlk_apply_of_mem hinj01] at hentry
    simpa only [Units.val_one, Matrix.one_apply, hinj01.eq_iff] using hentry
  have hPhi_inj : Function.Injective Phi := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hk := hkron a ha
    have h0 : a 0 = 1 := Subtype.ext (nsKron_eq_one (Matrix.SpecialLinearGroup.det_coe (a 0)) hk).1
    have h1 : a 1 = 1 := Subtype.ext (nsKron_eq_one (Matrix.SpecialLinearGroup.det_coe (a 0)) hk).2
    have h2 : a 2 = 1 := by
      have h23' : nsKron (K := K) 1 (↑(a 2) : Matrix (Fin 2) (Fin 2) K) = 1 := by
        ext p q
        have hentry := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
          (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (pairEmb i2 i3 p)
            (pairEmb i2 i3 q)) ha
        rw [hPhi_apply a] at hentry
        rw [show ((L (a 0) * R (a 1) * R' (a 2) : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
            nsBlk (K := K) (pairEmb i0 i1)
              (nsKron (↑(a 0) : Matrix (Fin 2) (Fin 2) K) (↑(a 1) : Matrix (Fin 2) (Fin 2) K)) *
              nsBlk (K := K) (pairEmb i2 i3) (nsKron 1 (↑(a 2) : Matrix (Fin 2) (Fin 2) K))
            from by
          rw [Units.val_mul, Units.val_mul, coe_nsLhom, coe_nsRhom, coe_nsRhom,
            nsBlk_mul hinj01, ← nsKron_mul_mul]
          simp [Matrix.mul_one, Matrix.one_mul]] at hentry
        rw [nsBlk_mul_nsBlk_apply_of_not_mem_left h23 hdisj] at hentry
        simpa only [Units.val_one, Matrix.one_apply, hinj23.eq_iff] using hentry
      exact Subtype.ext (nsKron_eq_one_right h23')
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have hcomm : ∀ a c, Phi a * Y c = Y c * Phi a := by
    intro a c
    have hYL : Commute (Y c) (L (a 0)) :=
      nsBlkHom_commute_of_disjoint hinj23 hinj01 hdisj.symm
        (nsKronLeftUnit (nsRootEl (Multiplicative.toAdd c))) (nsKronLeftUnit (a 0))
    have hYR : Commute (Y c) (R (a 1)) :=
      nsBlkHom_commute_of_disjoint hinj23 hinj01 hdisj.symm
        (nsKronLeftUnit (nsRootEl (Multiplicative.toAdd c))) (nsKronRightUnit (a 1))
    have hYR' : Commute (Y c) (R' (a 2)) :=
      (nsKronLeftUnit_commute (nsRootEl (Multiplicative.toAdd c)) (a 2)).map (nsBlkHom hinj23)
    rw [hPhi_apply a]
    exact ((hYL.mul_right hYR).mul_right hYR').symm.eq
  exact ⟨Phi, Y, hPhi_inj, hPhiO, hYO, hY1, hY2, hcomm⟩


end TableBSymp

end CFSG.StandardType

end
