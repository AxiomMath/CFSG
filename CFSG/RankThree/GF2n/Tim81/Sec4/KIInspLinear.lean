module

public import CFSG.CGT.Timmesfeld75.ListWCLinMain
public import CFSG.CGT.Timmesfeld75.TransvectionBasic
public import CFSG.GroupTheory.OddOrderClosurePerfect
public import CFSG.Quasithin.Background.HSL3Pair
public import CFSG.LinearAlgebra.ElationInvariantSubspace
public import CFSG.Timmesfeld.ARS.LinearLevis
public import CFSG.CGT.Timmesfeld75.ListWCLinSylow

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private abbrev SLn (n : ℕ) (K : Type*) [Field K] := SpecialLinearGroup (Fin n) K

private def i0 (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

private def iLast (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

private def midEmb (hn : 2 ≤ n) : Fin (n - 2) ↪ Fin n where
  toFun i := ⟨i.val + 1, by
    have hi := i.isLt
    have hn' : n - 2 + 2 = n := by omega
    omega⟩
  inj' i j h := by
    have h' := congrArg Fin.val h
    exact Fin.ext (by simp only at h'; omega)

@[simp]
private lemma midEmb_val (hn : 2 ≤ n) (i : Fin (n - 2)) : ((midEmb hn i : Fin n) : ℕ) = i.val + 1 :=
  rfl

private noncomputable def midMat (hn : 2 ≤ n) (A : Matrix (Fin (n - 2)) (Fin (n - 2)) K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.reindexAlgEquiv K K (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn))
    (Matrix.fromBlocks A 0 0 1)

private noncomputable def midBlock (hn : 2 ≤ n) : SpecialLinearGroup (Fin (n - 2)) K →*
    SpecialLinearGroup (Fin n) K where
  toFun A := ⟨midMat hn (A : Matrix (Fin (n - 2)) (Fin (n - 2)) K), by
    rw [midMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, A.2, one_mul,
      Matrix.det_one]⟩
  map_one' := Subtype.ext (by
    change midMat hn
      ((1 : SpecialLinearGroup (Fin (n - 2)) K) : Matrix (Fin (n - 2)) (Fin (n - 2)) K) = 1
    rw [midMat, Matrix.SpecialLinearGroup.coe_one, Matrix.fromBlocks_one, map_one])
  map_mul' A B := Subtype.ext (by
    change midMat hn
      ((A * B : SpecialLinearGroup (Fin (n - 2)) K) :
        Matrix (Fin (n - 2)) (Fin (n - 2)) K) =
      midMat hn (A : Matrix (Fin (n - 2)) (Fin (n - 2)) K) *
        midMat hn (B : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
    rw [midMat, midMat, midMat, Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      Matrix.fromBlocks_multiply]
    simp)

private abbrev C (hn : 2 ≤ n) := {a : Fin n // a ∉ Set.range (midEmb hn)}

private def c0 (hn : 2 ≤ n) : C hn := ⟨i0 hn, by
  rintro ⟨i, hi⟩
  have h1 : (i.val : ℕ) + 1 = 0 := by
    simpa only [midEmb_val, i0, Fin.val_mk] using congrArg Fin.val hi
  omega⟩

private def cL (hn : 2 ≤ n) : C hn := ⟨iLast hn, by
  rintro ⟨i, hi⟩
  have h1 : (i.val : ℕ) + 1 = n - 1 := by
    simpa only [midEmb_val, iLast, Fin.val_mk] using congrArg Fin.val hi
  have := i.isLt
  omega⟩

private lemma midEmb_lt_midEmb (hn : 2 ≤ n) {i j : Fin (n - 2)} :
    midEmb hn i < midEmb hn j ↔ i < j := by
  constructor
  · intro h
    have h' : (midEmb hn i).val < (midEmb hn j).val := h
    simp only [midEmb_val] at h'
    omega
  · intro h
    show (midEmb hn i).val < (midEmb hn j).val
    simp only [midEmb_val]
    omega

private lemma i0_lt_midEmb (hn : 2 ≤ n) (i : Fin (n - 2)) : i0 hn < midEmb hn i := by
  show (i0 hn).val < (midEmb hn i).val
  simp [i0, midEmb_val]

private lemma midEmb_lt_iLast (hn : 2 ≤ n) (i : Fin (n - 2)) : midEmb hn i < iLast hn := by
  show (midEmb hn i).val < (iLast hn).val
  simp only [midEmb_val, iLast, Fin.val_mk]
  have := i.isLt
  omega

private lemma i0_ne_midEmb (hn : 2 ≤ n) (i : Fin (n - 2)) : i0 hn ≠ midEmb hn i :=
  (i0_lt_midEmb hn i).ne

private lemma midEmb_ne_iLast (hn : 2 ≤ n) (i : Fin (n - 2)) : midEmb hn i ≠ iLast hn :=
  (midEmb_lt_iLast hn i).ne

private lemma i0_lt_iLast (hn : 2 ≤ n) : i0 hn < iLast hn := by
  show (i0 hn).val < (iLast hn).val
  simp [i0, iLast]
  omega

private lemma C_eq_c0_or_cL (hn : 2 ≤ n) (j : C hn) : j = c0 hn ∨ j = cL hn := by
  rcases Nat.eq_zero_or_pos j.1.val with h0 | hpos
  · left
    apply Subtype.ext
    apply Fin.ext
    simp [c0, i0, h0]
  · by_cases hlast : j.1.val = n - 1
    · right
      apply Subtype.ext
      apply Fin.ext
      simp [cL, iLast, hlast]
    · exfalso
      apply j.2
      refine ⟨⟨j.1.val - 1, by omega⟩, ?_⟩
      apply Fin.ext
      show (midEmb hn ⟨j.1.val - 1, by omega⟩).val = j.1.val
      simp only [midEmb_val]
      omega

private lemma c0_ne_cL (hn : 2 ≤ n) : c0 hn ≠ cL hn := by
  intro h
  have := congrArg (fun x : C hn => (x : Fin n)) h
  simp only [c0, cL, i0, iLast, Fin.mk.injEq] at this
  omega

private lemma cL_ne_c0 (hn : 2 ≤ n) : cL hn ≠ c0 hn := (c0_ne_cL hn).symm

private def Avec (hn : 2 ≤ n) (b : Fin (n - 2) → K) : Matrix (Fin (n - 2)) (C hn) K :=
  fun i j => if j = cL hn then b i else 0

private def Bvec (hn : 2 ≤ n) (a : Fin (n - 2) → K) : Matrix (C hn) (Fin (n - 2)) K :=
  fun i j => if i = c0 hn then a j else 0

private def Emat (hn : 2 ≤ n) (c : K) : Matrix (C hn) (C hn) K :=
  fun i j => if i = c0 hn ∧ j = cL hn then c else 0

private def Dvec (hn : 2 ≤ n) (c : K) : Matrix (C hn) (C hn) K :=
  1 + Emat hn c

private noncomputable def CEquivFinTwo (hn : 2 ≤ n) : C hn ≃ Fin 2 where
  toFun j := if j = c0 hn then 0 else 1
  invFun k := if k = 0 then c0 hn else cL hn
  left_inv j := by
    rcases C_eq_c0_or_cL hn j with rfl | rfl <;> simp [c0_ne_cL hn, cL_ne_c0 hn]
  right_inv k := by
    fin_cases k <;> simp [c0_ne_cL hn, cL_ne_c0 hn]

private noncomputable def outerDiag (hn : 2 ≤ n) (α β : K) : Matrix (C hn) (C hn) K :=
  Matrix.diagonal (fun i => if i = c0 hn then α else β)

private noncomputable def diagFull (hn : 2 ≤ n) (ν : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.reindexAlgEquiv K K (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn))
    (Matrix.fromBlocks (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
      (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
      (outerDiag hn (ν⁻¹ ^ (n - 1)) ν))

private lemma det_diagFull (hn : 2 ≤ n) (ν : K) (hν : ν ≠ 0) :
    (diagFull hn ν).det = 1 := by
  rw [diagFull, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, outerDiag,
    Matrix.det_diagonal]
  have hprod : (∏ i : C hn, (if i = c0 hn then ν⁻¹ ^ (n - 1) else ν)) =
      ν⁻¹ ^ (n - 1) * ν := by
    rw [Fintype.prod_equiv (CEquivFinTwo hn)
      (fun i : C hn => if i = c0 hn then ν⁻¹ ^ (n - 1) else ν)
      (fun k : Fin 2 => if k = 0 then ν⁻¹ ^ (n - 1) else ν)
      (fun i => by
        rcases C_eq_c0_or_cL hn i with rfl | rfl <;> simp [CEquivFinTwo])]
    simp [Fin.prod_univ_two]
  rw [hprod, inv_pow]
  field_simp [hν, pow_ne_zero]
  rw [← pow_succ]
  have hpow : n - 2 + 1 = n - 1 := by omega
  rw [hpow]

private lemma Avec_mul_outerDiag (hn : 2 ≤ n) (α β : K) (b : Fin (n - 2) → K) :
    Avec hn b * outerDiag hn α β = Avec hn (β • b) := by
  ext i j
  rw [Avec, outerDiag, Matrix.mul_diagonal]
  rcases C_eq_c0_or_cL hn j with rfl | rfl <;>
    simp [Avec, Pi.smul_apply, cL_ne_c0 hn, c0_ne_cL hn, mul_comm]

private lemma outerDiag_mul_Bvec (hn : 2 ≤ n) (α β : K) (a : Fin (n - 2) → K) :
    outerDiag hn α β * Bvec hn a = Bvec hn (α • a) := by
  ext i j
  rw [Bvec, outerDiag, Matrix.diagonal_mul]
  rcases C_eq_c0_or_cL hn i with rfl | rfl <;> simp [Bvec, Pi.smul_apply, c0_ne_cL hn, cL_ne_c0 hn]

private lemma outerDiag_inv (hn : 2 ≤ n) (α β : K) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (outerDiag hn α β)⁻¹ = outerDiag hn α⁻¹ β⁻¹ := by
  apply Matrix.inv_eq_right_inv
  ext i j
  rw [outerDiag, Matrix.diagonal_mul]
  rcases C_eq_c0_or_cL hn i with rfl | rfl <;>
    rcases C_eq_c0_or_cL hn j with rfl | rfl <;>
    simp [outerDiag, Matrix.one_apply, hα, hβ, c0_ne_cL hn, cL_ne_c0 hn]

private lemma outerDiag_mul_inv (hn : 2 ≤ n) (α β : K) (hα : α ≠ 0) (hβ : β ≠ 0) :
    outerDiag hn α β * (outerDiag hn α β)⁻¹ = 1 := by
  rw [outerDiag_inv hn α β hα hβ]
  ext i j
  rw [outerDiag, Matrix.diagonal_mul]
  rcases C_eq_c0_or_cL hn i with rfl | rfl <;>
    rcases C_eq_c0_or_cL hn j with rfl | rfl <;>
    simp [outerDiag, Matrix.one_apply, hα, hβ, c0_ne_cL hn, cL_ne_c0 hn]

private lemma Avec_mul_outerDiag_inv (hn : 2 ≤ n) (α β : K) (hα : α ≠ 0)
    (hβ : β ≠ 0) (b : Fin (n - 2) → K) :
    Avec hn b * (outerDiag hn α β)⁻¹ = Avec hn (β⁻¹ • b) := by
  rw [outerDiag_inv hn α β hα hβ, Avec_mul_outerDiag]

private lemma outerDiag_mul_Dvec_mul_inv (hn : 2 ≤ n) (α β : K) (hα : α ≠ 0)
    (hβ : β ≠ 0) (c : K) :
    outerDiag hn α β * Dvec hn c * (outerDiag hn α β)⁻¹ =
      Dvec hn (α * β⁻¹ * c) := by
  rw [outerDiag_inv hn α β hα hβ, outerDiag, outerDiag]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases C_eq_c0_or_cL hn i with rfl | rfl <;>
    rcases C_eq_c0_or_cL hn j with rfl | rfl <;>
    simp [Dvec, Emat, Matrix.one_apply, hα, hβ, c0_ne_cL hn, cL_ne_c0 hn,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private lemma Avec_add (hn : 2 ≤ n) (b b' : Fin (n - 2) → K) :
    Avec hn b + Avec hn b' = Avec hn (b + b') := by
  ext i j
  by_cases h : j = cL hn <;> simp [Avec, h]

private lemma Bvec_add (hn : 2 ≤ n) (a a' : Fin (n - 2) → K) :
    Bvec hn a + Bvec hn a' = Bvec hn (a + a') := by
  ext i j
  by_cases h : i = c0 hn <;> simp [Bvec, h]

private lemma Emat_add (hn : 2 ≤ n) (c c' : K) :
    Emat hn c + Emat hn c' = Emat hn (c + c') := by
  ext i j
  by_cases h : i = c0 hn ∧ j = cL hn <;> simp [Emat, h]

private lemma Emat_add_Dvec (hn : 2 ≤ n) (x c : K) :
    Emat hn x + Dvec hn c = Dvec hn (c + x) := by
  rw [Dvec, Dvec, add_comm (Emat hn x) (1 + Emat hn c), add_assoc, Emat_add]

private lemma mul_Avec (hn : 2 ≤ n) (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
    (b : Fin (n - 2) → K) :
    M * Avec hn b = Avec hn (M *ᵥ b) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : j = cL hn
  · subst hj
    simp [Avec, Matrix.mulVec, dotProduct]
  · simp [Avec, hj]

private lemma Bvec_mul (hn : 2 ≤ n) (a : Fin (n - 2) → K)
    (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) :
    Bvec hn a * M = Bvec hn (a ᵥ* M) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i = c0 hn
  · subst hi
    simp [Bvec, Matrix.vecMul, dotProduct]
  · simp [Bvec, hi]

private lemma Dvec_add_Emat (hn : 2 ≤ n) (c x : K) :
    Dvec hn c + Emat hn x = Dvec hn (c + x) := by
  rw [add_comm, Emat_add_Dvec]

private lemma Avec_mul_Bvec (hn : 2 ≤ n) (b a : Fin (n - 2) → K) :
    Avec hn b * Bvec hn a = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = cL hn
  · subst hk
    simp [Avec, Bvec, cL_ne_c0 hn]
  · simp [Avec, hk]

private lemma Avec_mul_Emat (hn : 2 ≤ n) (b : Fin (n - 2) → K) (c : K) :
    Avec hn b * Emat hn c = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = c0 hn
  · subst hk
    simp [Avec, c0_ne_cL hn]
  · simp [Emat, hk]

private lemma Avec_mul_Dvec (hn : 2 ≤ n) (b : Fin (n - 2) → K) (c : K) :
    Avec hn b * Dvec hn c = Avec hn b := by
  rw [Dvec, Matrix.mul_add, Matrix.mul_one, Avec_mul_Emat, add_zero]

private lemma Emat_mul_Bvec (hn : 2 ≤ n) (a : Fin (n - 2) → K) (c : K) :
    Emat hn c * Bvec hn a = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = cL hn
  · subst hk
    simp [Bvec, cL_ne_c0 hn, c0_ne_cL hn, eq_comm]
  · simp [Emat, hk]

private lemma Dvec_mul_Bvec (hn : 2 ≤ n) (a : Fin (n - 2) → K) (c : K) :
    Dvec hn c * Bvec hn a = Bvec hn a := by
  rw [Dvec, Matrix.add_mul, Matrix.one_mul, Emat_mul_Bvec, add_zero]

private lemma Bvec_mul_Avec (hn : 2 ≤ n) (a b : Fin (n - 2) → K) :
    Bvec hn a * Avec hn b = Emat hn (a ⬝ᵥ b) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i = c0 hn
  · subst hi
    by_cases hj : j = cL hn
    · subst hj
      simp [Bvec, Avec, Emat, dotProduct]
    · have hzero : ∀ x ∈ Finset.univ,
          (Bvec hn a) (c0 hn) x * (Avec hn b) x j = 0 := by
        intro x _
        simp [Avec, hj]
      rw [Finset.sum_eq_zero hzero]
      simp [Emat, hj]
  · have hzero : ∀ x ∈ Finset.univ, (Bvec hn a) i x * (Avec hn b) x j = 0 := by
      intro x _
      simp [Bvec, hi]
    rw [Finset.sum_eq_zero hzero]
    simp [Emat, hi]

private lemma Emat_mul_Emat (hn : 2 ≤ n) (c c' : K) :
    Emat hn c * Emat hn c' = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = c0 hn
  · subst hk
    simp [Emat, c0_ne_cL hn]
  · simp [Emat, hk]

private lemma Dvec_mul_Dvec (hn : 2 ≤ n) (c c' : K) :
    Dvec hn c * Dvec hn c' = Dvec hn (c + c') := by
  rw [Dvec, Dvec, Dvec, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one, Emat_mul_Emat, add_zero, add_assoc,
    add_comm (Emat hn c') (Emat hn c), ← Emat_add]

private lemma coe_midBlock (hn : 2 ≤ n) (M : SpecialLinearGroup (Fin (n - 2)) K) :
    (midBlock hn M : Matrix (Fin n) (Fin n) K) =
      Matrix.reindexAlgEquiv K K (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn))
        (Matrix.fromBlocks (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) 0 0 1) :=
  rfl

private noncomputable def cornerMat (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.reindexAlgEquiv K K (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn))
    (Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
      (Avec hn b) (Bvec hn a) (Dvec hn c))

private lemma cornerMat_mul (hn : 2 ≤ n) (a b a' b' : Fin (n - 2) → K) (c c' : K) :
    cornerMat hn a b c * cornerMat hn a' b' c' =
      cornerMat hn (a + a') (b + b') (c + c' + a ⬝ᵥ b') := by
  simp only [cornerMat]
  rw [← map_mul]
  have h : Matrix.fromBlocks 1 (Avec hn b) (Bvec hn a) (Dvec hn c) *
        Matrix.fromBlocks 1 (Avec hn b') (Bvec hn a') (Dvec hn c') =
      Matrix.fromBlocks 1 (Avec hn (b + b')) (Bvec hn (a + a'))
        (Dvec hn (c + c' + a ⬝ᵥ b')) := by
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_one, Matrix.one_mul, Avec_mul_Bvec, Avec_mul_Dvec, Bvec_mul_Avec,
      Dvec_mul_Bvec, Dvec_mul_Dvec, Emat_add_Dvec, Dvec_add_Emat, Avec_add, Bvec_add,
      add_comm, add_left_comm, add_assoc]
  rw [h]

private lemma cornerMat_conj (hn : 2 ≤ n) (M : SpecialLinearGroup (Fin (n - 2)) K)
    (a b : Fin (n - 2) → K) (c : K) :
    (midBlock hn M : Matrix (Fin n) (Fin n) K) * cornerMat hn a b c *
        (((midBlock hn M)⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
      cornerMat hn (a ᵥ* ((M⁻¹ : SpecialLinearGroup (Fin (n - 2)) K) :
        Matrix (Fin (n - 2)) (Fin (n - 2)) K))
        (((M : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K) *ᵥ b) c := by
  simp only [cornerMat]
  rw [← map_inv, coe_midBlock, coe_midBlock, ← map_mul, ← map_mul]
  have h : Matrix.fromBlocks (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) 0 0 1 *
        Matrix.fromBlocks 1 (Avec hn b) (Bvec hn a) (Dvec hn c) *
        Matrix.fromBlocks ((M⁻¹ : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K) 0 0 1 =
      Matrix.fromBlocks 1
        (Avec hn (((M : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K) *ᵥ b))
        (Bvec hn (a ᵥ* ((M⁻¹ : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K))) (Dvec hn c) := by
    have hMM : (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) *
        ((M⁻¹ : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hM'M : ((M⁻¹ : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K) *
        (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, hMM, hM'M, mul_Avec, Bvec_mul]
  rw [h]

private lemma midBlock_conj_apply (hn : 2 ≤ n)
    (A : SpecialLinearGroup (Fin (n - 2)) K) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin (n - 2)) :
    ((midBlock hn A : Matrix (Fin n) (Fin n) K) * X *
        (((midBlock hn A)⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) (midEmb hn i) (midEmb hn j) =
      ((A : Matrix (Fin (n - 2)) (Fin (n - 2)) K) *
        (Matrix.of fun a b => X (midEmb hn a) (midEmb hn b)) *
        ((A⁻¹ : SpecialLinearGroup (Fin (n - 2)) K) :
          Matrix (Fin (n - 2)) (Fin (n - 2)) K)) i j := by
  let e := CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)
  let X' : Matrix (Fin (n - 2) ⊕ C hn) (Fin (n - 2) ⊕ C hn) K :=
    Matrix.reindexAlgEquiv K K e.symm X
  have hX : X = Matrix.reindexAlgEquiv K K e X' := by
    ext a b
    simp [X', Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  let X11 : Matrix (Fin (n - 2)) (Fin (n - 2)) K :=
    fun a b => X' (Sum.inl a) (Sum.inl b)
  let X12 : Matrix (Fin (n - 2)) (C hn) K := fun a b => X' (Sum.inl a) (Sum.inr b)
  let X21 : Matrix (C hn) (Fin (n - 2)) K := fun a b => X' (Sum.inr a) (Sum.inl b)
  let X22 : Matrix (C hn) (C hn) K := fun a b => X' (Sum.inr a) (Sum.inr b)
  have hX' : X' = Matrix.fromBlocks X11 X12 X21 X22 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> rfl
  have hX11 : (Matrix.of fun a b =>
      (Matrix.reindexAlgEquiv K K e X') (midEmb hn a) (midEmb hn b)) = X11 := by
    ext a b
    have ha : e.symm (midEmb hn a) = Sum.inl a := by
      rw [← CFSG.Timmesfeld.ARS.Linear.embEquiv_inl (midEmb hn) a, e.symm_apply_apply]
    have hb : e.symm (midEmb hn b) = Sum.inl b := by
      rw [← CFSG.Timmesfeld.ARS.Linear.embEquiv_inl (midEmb hn) b, e.symm_apply_apply]
    simp [X11, Matrix.reindexAlgEquiv_apply, ha, hb]
  rw [hX, ← map_inv, coe_midBlock, coe_midBlock]
  rw [show midEmb hn i = e (Sum.inl i) from (CFSG.Timmesfeld.ARS.Linear.embEquiv_inl
    (midEmb hn) i).symm,
    show midEmb hn j = e (Sum.inl j) from (CFSG.Timmesfeld.ARS.Linear.embEquiv_inl
    (midEmb hn) j).symm]
  rw [← map_mul, ← map_mul, hX11, hX', Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.reindexAlgEquiv_apply, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_one, Matrix.one_mul]
  dsimp only [e]
  rw [Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simp [Matrix.fromBlocks_apply₁₁]

private noncomputable def revSL (m : ℕ) : SpecialLinearGroup (Fin m) K :=
  ⟨Matrix.permMatrixHom (Fin.revPerm : Equiv.Perm (Fin m)), by
    rw [Matrix.permMatrixHom_apply, Matrix.det_permutation, Equiv.Perm.inv_def, Fin.revPerm_symm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h
    · rw [h]
      simp
    · rw [h]
      simpa using CharTwo.neg_eq (1 : K)⟩

private lemma revSL_conj_apply (m : ℕ) (X : Matrix (Fin m) (Fin m) K) (a b : Fin m) :
    ((revSL (K := K) m : Matrix (Fin m) (Fin m) K) * X *
        (((revSL (K := K) m)⁻¹ : SpecialLinearGroup (Fin m) K) :
          Matrix (Fin m) (Fin m) K)) a b =
      X (Fin.revPerm a) (Fin.revPerm b) := by
  have hww : revSL (K := K) m * revSL (K := K) m = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    change Matrix.permMatrixHom (Fin.revPerm : Equiv.Perm (Fin m)) *
      Matrix.permMatrixHom (Fin.revPerm : Equiv.Perm (Fin m)) = 1
    rw [← map_mul, show (Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm = 1 from
      Equiv.ext fun x => by simpa [Fin.revPerm_apply] using Fin.rev_rev x, map_one]
  have hinv : (revSL (K := K) m)⁻¹ = revSL (K := K) m := inv_eq_of_mul_eq_one_right hww
  rw [hinv]
  change ((Matrix.permMatrixHom (Fin.revPerm : Equiv.Perm (Fin m)) * X *
    Matrix.permMatrixHom (Fin.revPerm : Equiv.Perm (Fin m))) :
      Matrix (Fin m) (Fin m) K) a b = _
  simpa [Equiv.Perm.inv_def] using
    CFSG.LinearAlgebra.permMatrixHom_conj_apply (K := K) (m := m) Fin.revPerm X a b

private lemma embEquiv_symm_i0 (hn : 2 ≤ n) :
    (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)).symm (i0 hn) = Sum.inr (c0 hn) := by
  rw [Equiv.symm_apply_eq]
  exact (CFSG.Timmesfeld.ARS.Linear.embEquiv_inr (midEmb hn) (c0 hn)).symm

private lemma embEquiv_symm_iLast (hn : 2 ≤ n) :
    (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)).symm (iLast hn) = Sum.inr (cL hn) := by
  rw [Equiv.symm_apply_eq]
  exact (CFSG.Timmesfeld.ARS.Linear.embEquiv_inr (midEmb hn) (cL hn)).symm

private lemma embEquiv_symm_mid (hn : 2 ≤ n) (i : Fin (n - 2)) :
    (CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)).symm (midEmb hn i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact (CFSG.Timmesfeld.ARS.Linear.embEquiv_inl (midEmb hn) i).symm

private lemma cornerMat_apply_i0_i0 (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K) :
    cornerMat hn a b c (i0 hn) (i0 hn) = 1 := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_i0, Matrix.fromBlocks_apply₂₂]
  simp [Dvec, Emat, Matrix.one_apply, c0_ne_cL hn]

private lemma cornerMat_apply_i0_iLast (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K) :
    cornerMat hn a b c (i0 hn) (iLast hn) = c := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_i0, embEquiv_symm_iLast,
    Matrix.fromBlocks_apply₂₂]
  change (1 + Emat hn c) (c0 hn) (cL hn) = c
  rw [Matrix.add_apply, Matrix.one_apply, Emat]
  simp [c0_ne_cL hn]

private lemma cornerMat_apply_i0_mid (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K)
    (j : Fin (n - 2)) : cornerMat hn a b c (i0 hn) (midEmb hn j) = a j := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_i0, embEquiv_symm_mid,
    Matrix.fromBlocks_apply₂₁]
  simp [Bvec]

private lemma cornerMat_apply_iLast_i0 (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K) :
    cornerMat hn a b c (iLast hn) (i0 hn) = 0 := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_iLast, embEquiv_symm_i0,
    Matrix.fromBlocks_apply₂₂]
  change (1 + Emat hn c) (cL hn) (c0 hn) = 0
  rw [Matrix.add_apply, Matrix.one_apply, Emat]
  simp [cL_ne_c0 hn, c0_ne_cL hn]

private lemma cornerMat_apply_iLast_iLast (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K) :
    cornerMat hn a b c (iLast hn) (iLast hn) = 1 := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_iLast, Matrix.fromBlocks_apply₂₂]
  simp [Dvec, Emat, Matrix.one_apply, c0_ne_cL hn, cL_ne_c0 hn]

private lemma cornerMat_apply_iLast_mid (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K)
    (j : Fin (n - 2)) : cornerMat hn a b c (iLast hn) (midEmb hn j) = 0 := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_iLast, embEquiv_symm_mid,
    Matrix.fromBlocks_apply₂₁]
  change (if cL hn = c0 hn then a j else 0) = 0
  rw [if_neg (cL_ne_c0 hn)]

private lemma cornerMat_apply_mid_i0 (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K)
    (i : Fin (n - 2)) : cornerMat hn a b c (midEmb hn i) (i0 hn) = 0 := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_mid, embEquiv_symm_i0,
    Matrix.fromBlocks_apply₁₂]
  simp [Avec, c0_ne_cL hn]

private lemma cornerMat_apply_mid_iLast (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K)
    (i : Fin (n - 2)) : cornerMat hn a b c (midEmb hn i) (iLast hn) = b i := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_mid, embEquiv_symm_iLast,
    Matrix.fromBlocks_apply₁₂]
  simp [Avec]

private lemma cornerMat_apply_mid_mid (hn : 2 ≤ n) (a b : Fin (n - 2) → K) (c : K)
    (i j : Fin (n - 2)) :
    cornerMat hn a b c (midEmb hn i) (midEmb hn j) = if i = j then 1 else 0 := by
  rw [cornerMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, embEquiv_symm_mid, embEquiv_symm_mid,
    Matrix.fromBlocks_apply₁₁]
  simp [Matrix.one_apply]

private lemma eq_zero_or_eq_last_or_mid (hn : 2 ≤ n) (i : Fin n) :
    i = i0 hn ∨ i = iLast hn ∨ ∃ j : Fin (n - 2), i = midEmb hn j := by
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · left
    apply Fin.ext
    simp [i0, h0]
  · by_cases hlast : i.val = n - 1
    · right
      left
      apply Fin.ext
      simp [iLast, hlast]
    · right
      right
      refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      apply Fin.ext
      show i.val = (midEmb hn ⟨i.val - 1, by omega⟩).val
      rw [midEmb_val]
      simp only [Fin.val_mk]
      omega

private lemma midBlock_part_eq_one
    (hn : 2 ≤ n) {T : Subgroup (SLn n K)} (hTU : T ≤ unitriangular n K)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock hn A ∈ Subgroup.normalizer (T : Set (SLn n K)))
    {x : SLn n K} (hxT : x ∈ T) :
    (Matrix.of fun i j : Fin (n - 2) =>
      (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (midEmb hn j)) = 1 := by
  let X11 : Matrix (Fin (n - 2)) (Fin (n - 2)) K :=
    Matrix.of fun i j => (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (midEmb hn j)
  have hxU := hTU hxT
  have hx_lower := (mem_unitriangular.mp hxU).1
  have hx_diag := (mem_unitriangular.mp hxU).2
  have hrevN : midBlock hn (revSL (K := K) (n - 2)) ∈
      Subgroup.normalizer (T : Set (SLn n K)) := hG0 _
  have hyT : midBlock hn (revSL (K := K) (n - 2)) * x *
      (midBlock hn (revSL (K := K) (n - 2)))⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hrevN x).mp hxT
  have hy_lower := (mem_unitriangular.mp (hTU hyT)).1
  have hX11_lower : ∀ a b : Fin (n - 2), a < b → X11 a b = 0 := by
    intro a b hab
    have hlt : Fin.revPerm b < Fin.revPerm a := Fin.rev_lt_rev.mpr hab
    have hlt' : midEmb hn (Fin.revPerm b) < midEmb hn (Fin.revPerm a) :=
      (midEmb_lt_midEmb hn).mpr hlt
    have hy0 : (midBlock hn (revSL (K := K) (n - 2)) * x *
        (midBlock hn (revSL (K := K) (n - 2)))⁻¹ : SLn n K)
        (midEmb hn (Fin.revPerm a)) (midEmb hn (Fin.revPerm b)) = 0 :=
      hy_lower _ _ hlt'
    have hy0' : ((midBlock hn (revSL (K := K) (n - 2)) : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) K) *
        (((midBlock hn (revSL (K := K) (n - 2)))⁻¹ : SLn n K) :
          Matrix (Fin n) (Fin n) K))
        (midEmb hn (Fin.revPerm a)) (midEmb hn (Fin.revPerm b)) = 0 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using hy0
    have hconj := midBlock_conj_apply hn (revSL (K := K) (n - 2))
      (x : Matrix (Fin n) (Fin n) K) (Fin.revPerm a) (Fin.revPerm b)
    rw [hconj] at hy0'
    rw [revSL_conj_apply] at hy0'
    simpa [X11, Fin.revPerm_apply] using hy0'
  have hX11 : X11 = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [show X11 i i = (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (midEmb hn i) from rfl,
        hx_diag (midEmb hn i), Matrix.one_apply_eq]
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · rw [hX11_lower i j hlt, Matrix.one_apply_ne hij]
      · rw [show X11 i j = (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (midEmb hn j) from rfl,
          hx_lower (midEmb hn i) (midEmb hn j) ((midEmb_lt_midEmb hn).mpr hgt),
          Matrix.one_apply_ne hij]
  simpa [X11] using hX11

private lemma exists_corner_of_mem_of_midBlock
    (hn : 2 ≤ n) {x : SLn n K} (hxU : x ∈ unitriangular n K)
    (hmid : (Matrix.of fun i j : Fin (n - 2) =>
      (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (midEmb hn j)) = 1) :
    ∃ a b : Fin (n - 2) → K, ∃ c : K,
      (x : Matrix (Fin n) (Fin n) K) = cornerMat hn a b c := by
  have hx_lower := (mem_unitriangular.mp hxU).1
  have hx_diag := (mem_unitriangular.mp hxU).2
  have hmid_apply : ∀ i j : Fin (n - 2),
      (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (midEmb hn j) =
        if i = j then 1 else 0 := by
    intro i j
    simpa [Matrix.one_apply] using congrFun (congrFun hmid i) j
  let a : Fin (n - 2) → K := fun j => (x : Matrix (Fin n) (Fin n) K) (i0 hn) (midEmb hn j)
  let b : Fin (n - 2) → K := fun i => (x : Matrix (Fin n) (Fin n) K) (midEmb hn i) (iLast hn)
  let c : K := (x : Matrix (Fin n) (Fin n) K) (i0 hn) (iLast hn)
  refine ⟨a, b, c, ?_⟩
  ext i j
  rcases eq_zero_or_eq_last_or_mid hn i with rfl | rfl | ⟨i', rfl⟩ <;>
    rcases eq_zero_or_eq_last_or_mid hn j with rfl | rfl | ⟨j', rfl⟩ <;>
    simp [a, b, c, cornerMat_apply_i0_i0, cornerMat_apply_i0_iLast,
      cornerMat_apply_i0_mid, cornerMat_apply_iLast_i0, cornerMat_apply_iLast_iLast,
      cornerMat_apply_iLast_mid, cornerMat_apply_mid_i0, cornerMat_apply_mid_iLast,
      cornerMat_apply_mid_mid, hx_diag, hx_lower, hmid_apply, i0_lt_midEmb,
      midEmb_lt_iLast,
      i0_lt_iLast]

private lemma exists_corner_of_mem
    (hn : 4 ≤ n) {T : Subgroup (SLn n K)} (hTU : T ≤ unitriangular n K)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock (show 2 ≤ n by omega) A ∈ Subgroup.normalizer (T : Set (SLn n K))) :
    ∀ x ∈ T, ∃ a b : Fin (n - 2) → K, ∃ c : K,
      (x : Matrix (Fin n) (Fin n) K) = cornerMat (show 2 ≤ n by omega) a b c := by
  intro x hxT
  let hn2 : 2 ≤ n := by omega
  exact exists_corner_of_mem_of_midBlock hn2 (hTU hxT)
    (midBlock_part_eq_one hn2 hTU (fun A => hG0 A) hxT)

private lemma cornerMat_inj (hn : 2 ≤ n) {a b a' b' : Fin (n - 2) → K} {c c' : K}
    (h : cornerMat hn a b c = cornerMat hn a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  refine ⟨?_, ?_, ?_⟩
  · funext j
    simpa [cornerMat_apply_i0_mid] using
      congrFun (congrFun h (i0 hn)) (midEmb hn j)
  · funext i
    simpa [cornerMat_apply_mid_iLast] using
      congrFun (congrFun h (midEmb hn i)) (iLast hn)
  · simpa [cornerMat_apply_i0_iLast] using
      congrFun (congrFun h (i0 hn)) (iLast hn)

private lemma corner_commutator_block
    (hn : 4 ≤ n) (M : SpecialLinearGroup (Fin (n - 2)) K) (s : K)
    {i j : Fin (n - 2)} (hij : i ≠ j)
    (hM : (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) = Matrix.transvection i j s)
    (a b : Fin (n - 2) → K) (c : K)
    (hx2 : cornerMat (show 2 ≤ n by omega) a b c *
      cornerMat (show 2 ≤ n by omega) a b c = 1) :
    ((midBlock (show 2 ≤ n by omega) M : Matrix (Fin n) (Fin n) K) *
        cornerMat (show 2 ≤ n by omega) a b c *
        (((midBlock (show 2 ≤ n by omega) M)⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *
        (cornerMat (show 2 ≤ n by omega) a b c)⁻¹) =
      cornerMat (show 2 ≤ n by omega) (Pi.single j (s * a i))
        (Pi.single i (s * b j)) (a ⬝ᵥ b + s * a i * b j) := by
  let hn2 : 2 ≤ n := by omega
  have hM2 : (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) *
      (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) = 1 := by
    rw [hM, Matrix.transvection_mul_transvection_same i j hij,
      CharTwo.add_self_eq_zero, Matrix.transvection_zero]
  have hMinv : M⁻¹ = M := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hM2]
  have hcx : (cornerMat hn2 a b c)⁻¹ = cornerMat hn2 a b c :=
    Matrix.inv_eq_right_inv hx2
  have hrow : a ᵥ* (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) =
      a + Pi.single j (s * a i) := by
    rw [hM, ← CFSG.Quasithin.H.SL3Pair.transvection_transpose' j i s,
      Matrix.vecMul_transpose, CFSG.Quasithin.H.transvection_mulVec]
  have hcol : (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) *ᵥ b =
      b + Pi.single i (s * b j) := by
    rw [hM, CFSG.Quasithin.H.transvection_mulVec]
  have hconj := cornerMat_conj hn2 M a b c
  rw [hMinv, hrow, hcol] at hconj
  rw [hcx, hconj, cornerMat_mul]
  have hA : (a + Pi.single j (s * a i)) + a = Pi.single j (s * a i) := by
    ext k
    simp only [Pi.add_apply]
    linear_combination (a k) * CharTwo.two_eq_zero (R := K)
  have hB : (b + Pi.single i (s * b j)) + b = Pi.single i (s * b j) := by
    ext k
    simp only [Pi.add_apply]
    linear_combination (b k) * CharTwo.two_eq_zero (R := K)
  have hC : c + c + (a + Pi.single j (s * a i)) ⬝ᵥ b =
      a ⬝ᵥ b + s * a i * b j := by
    rw [CharTwo.add_self_eq_zero, zero_add, add_dotProduct, single_dotProduct]
  rw [hA, hB, hC]

private lemma cornerMat_zero (hn : 2 ≤ n) (c : K) :
    cornerMat hn 0 0 c = 1 + Matrix.single (i0 hn) (iLast hn) c := by
  let e := CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)
  have hblock : Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
        (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
        ((1 : Matrix (C hn) (C hn) K) + Matrix.single (c0 hn) (cL hn) c) =
      1 + Matrix.single (Sum.inr (c0 hn)) (Sum.inr (cL hn)) c := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simp [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Matrix.single_apply]
    · simp [Matrix.fromBlocks_apply₁₂, Matrix.one_apply, Matrix.single_apply]
    · simp [Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Matrix.single_apply]
    · by_cases ha : a = c0 hn
      · subst a
        by_cases hb : b = cL hn
        · subst b
          simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.single_apply]
        · have hb' : ¬ cL hn = b := fun h => hb h.symm
          simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.single_apply, hb, hb']
      · have ha' : ¬ c0 hn = a := fun h => ha h.symm
        simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.single_apply, ha, ha']
  have hcorner : cornerMat hn 0 0 c =
      Matrix.reindexAlgEquiv K K e
        (Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
          (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
          ((1 : Matrix (C hn) (C hn) K) + Matrix.single (c0 hn) (cL hn) c)) := by
    rw [cornerMat]
    change Matrix.reindexAlgEquiv K K e
        (Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
          (Avec hn 0) (Bvec hn 0) (Dvec hn c)) =
      Matrix.reindexAlgEquiv K K e
        (Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
          (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
          ((1 : Matrix (C hn) (C hn) K) + Matrix.single (c0 hn) (cL hn) c))
    apply_fun (Matrix.reindexAlgEquiv K K e).symm
    simp only [AlgEquiv.symm_apply_apply]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Avec, Bvec, Dvec, Emat, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.single_apply, eq_comm, and_comm]
  rw [hcorner, hblock, map_add, map_one, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Equiv.symm_symm,
    CFSG.Timmesfeld.ARS.Linear.embEquiv_inr,
    CFSG.Timmesfeld.ARS.Linear.embEquiv_inr]
  simp [c0, cL]

private lemma cornerMat_zero_zero (hn : 2 ≤ n) :
    cornerMat hn 0 0 (0 : K) = 1 := by
  rw [cornerMat_zero hn 0]
  simp

private lemma cornerMat_dot_eq_zero (hn : 4 ≤ n)
    {T : Subgroup (SpecialLinearGroup (Fin n) K)} (hT : Assembly.IsElemAbelian 2 T)
    {x : SpecialLinearGroup (Fin n) K} (hxT : x ∈ T)
    {a b : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) = cornerMat (show 2 ≤ n by omega) a b c) :
    a ⬝ᵥ b = 0 := by
  let hn2 : 2 ≤ n := by omega
  have hx2 : x * x = 1 := by
    have := hT.2 x hxT
    simpa [pow_two] using this
  have hx2m : (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using congrArg Subtype.val hx2
  have h1 : cornerMat hn2 (a + a) (b + b) (c + c + a ⬝ᵥ b) = 1 := by
    rw [← cornerMat_mul]
    rw [← hx, hx2m]
  have h2 : cornerMat hn2 (a + a) (b + b) (c + c + a ⬝ᵥ b) =
      cornerMat hn2 0 0 (0 : K) :=
    h1.trans (cornerMat_zero_zero hn2).symm
  have hcc : c + c = 0 := CharTwo.add_self_eq_zero c
  have := (cornerMat_inj hn2 h2).2.2
  rwa [hcc, zero_add] at this

private lemma exists_commutator_params (hn : 4 ≤ n) (hn2 : 2 ≤ n)
    {T : Subgroup (SpecialLinearGroup (Fin n) K)} (hT : Assembly.IsElemAbelian 2 T)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock hn2 A ∈ Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin n) K)))
    {x : SpecialLinearGroup (Fin n) K} (hxT : x ∈ T)
    {a b : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) = cornerMat hn2 a b c)
    {i j : Fin (n - 2)} (hij : i ≠ j) (s : K) :
    ∃ y ∈ T, ∃ c' : K,
      (y : Matrix (Fin n) (Fin n) K) =
        cornerMat hn2 (Pi.single j (s * a i)) (Pi.single i (s * b j)) c' := by
  let M : SpecialLinearGroup (Fin (n - 2)) K :=
    ⟨Matrix.transvection i j s, Matrix.det_transvection_of_ne i j hij s⟩
  have hM : (M : Matrix (Fin (n - 2)) (Fin (n - 2)) K) = Matrix.transvection i j s := rfl
  have hx2 : x * x = 1 := by
    have := hT.2 x hxT
    simpa [pow_two] using this
  have hx2m : (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using congrArg Subtype.val hx2
  have hx2c : cornerMat hn2 a b c * cornerMat hn2 a b c = 1 := by
    simpa [hx] using hx2m
  have hconjT : midBlock hn2 M * x * (midBlock hn2 M)⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp (hG0 M) x).mp hxT
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  let y : SpecialLinearGroup (Fin n) K := midBlock hn2 M * x * (midBlock hn2 M)⁻¹ * x
  have hyT : y ∈ T := T.mul_mem hconjT hxT
  refine ⟨y, hyT, a ⬝ᵥ b + s * a i * b j, ?_⟩
  have hcx : (cornerMat hn2 a b c)⁻¹ = cornerMat hn2 a b c :=
    Matrix.inv_eq_right_inv hx2c
  have hcomm := corner_commutator_block hn M s hij hM a b c hx2c
  simpa [y, hxinv, hcx, Matrix.SpecialLinearGroup.coe_mul, hx] using hcomm

private lemma exists_central_corner
    (hn : 4 ≤ n) {T : Subgroup (SLn n K)} (hTU : T ≤ unitriangular n K)
    (hB : upperTriangular n K ≤ Subgroup.normalizer (T : Set (SLn n K)))
    (hne : T ≠ ⊥) :
    ∃ u ∈ T, (u : SLn n K) ≠ 1 ∧ ∃ b : K, b ≠ 0 ∧
      (u : Matrix (Fin n) (Fin n) K) =
        1 + Matrix.single ⟨0, by omega⟩ ⟨n - 1, by omega⟩ b := by
  have hUN : unitriangular n K ≤ Subgroup.normalizer (T : Set (SLn n K)) :=
    le_trans (unitriangular_le_upperTriangular n K) hB
  haveI hNormal : (T.subgroupOf (unitriangular n K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTU).mpr hUN
  have hTne : T.subgroupOf (unitriangular n K) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hTU hx⟩ : unitriangular n K) ∈ T.subgroupOf (unitriangular n K) := hx
    rw [h, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    simpa using (congrArg Subtype.val (congrArg Subtype.val hx'))
  have hU2 : IsPGroup 2 (unitriangular n K) := by
    obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) (by omega)
    have := P.isPGroup'
    rwa [hP] at this
  have hUnil : Group.IsNilpotent (unitriangular n K) := hU2.isNilpotent
  obtain ⟨⟨u, huT, huZ⟩, hu1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hTne)
  have hu1' : (u : SLn n K) ≠ 1 := by
    intro h
    exact hu1 (Subtype.ext (Subtype.ext h))
  have hucomm : ∀ v ∈ unitriangular n K,
      (u : SLn n K) * v = v * (u : SLn n K) :=
    fun v hv => (congrArg Subtype.val (Subgroup.mem_center_iff.1 huZ ⟨v, hv⟩)).symm
  obtain ⟨b, hb⟩ := eq_one_add_single_of_commute_unitri (m := n) (by omega) u.2 hucomm
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hu1'
    apply Subtype.ext
    simpa using hb
  exact ⟨u, huT, hu1', b, hb0, hb⟩

private lemma midBlock_mem_normalizer_of_perfect
    (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K)
    {T : Subgroup (SLn n K)} {u : SLn n K} (huT : u ∈ T) (hu1 : u ≠ 1)
    {b : K} (hb : (u : Matrix (Fin n) (Fin n) K) =
      1 + Matrix.single ⟨0, by omega⟩ ⟨n - 1, by omega⟩ b)
    (hwti : ∀ t ∈ T, t ≠ 1 → ∀ y : SLn n K, y * t = t * y →
      Odd (orderOf y) → y ∈ Subgroup.normalizer (T : Set (SLn n K))) :
    ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock (show 2 ≤ n by omega) A ∈
        Subgroup.normalizer (T : Set (SLn n K)) := by
  let hn2 : 2 ≤ n := by omega
  have hperfect : Group.IsPerfect (SpecialLinearGroup (Fin (n - 2)) K) := by
    by_cases hn4 : n = 4
    · subst n
      simpa using CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K (hq rfl)
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  intro A
  have hcomm_of : ∀ C : SpecialLinearGroup (Fin (n - 2)) K,
      (midBlock hn2 C : Matrix (Fin n) (Fin n) K) * cornerMat hn2 0 0 b =
        cornerMat hn2 0 0 b * (midBlock hn2 C : Matrix (Fin n) (Fin n) K) := by
    intro C
    have hconj := cornerMat_conj hn2 C 0 0 b
    simp only [Matrix.zero_vecMul, Matrix.mulVec_zero] at hconj
    have hT'T : (((midBlock hn2 C)⁻¹ : SLn n K) :
          Matrix (Fin n) (Fin n) K) *
        (midBlock hn2 C : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h1 : ((midBlock hn2 C : Matrix (Fin n) (Fin n) K) *
        cornerMat hn2 0 0 b *
        (((midBlock hn2 C)⁻¹ : SLn n K) :
          Matrix (Fin n) (Fin n) K)) * (midBlock hn2 C :
            Matrix (Fin n) (Fin n) K) =
        (midBlock hn2 C : Matrix (Fin n) (Fin n) K) * cornerMat hn2 0 0 b := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hT'T, Matrix.mul_one]
    rw [hconj] at h1
    exact h1.symm
  have huform : (u : Matrix (Fin n) (Fin n) K) = cornerMat hn2 0 0 b := by
    have hb' : (u : Matrix (Fin n) (Fin n) K) =
        1 + Matrix.single (i0 hn2) (iLast hn2) b := by
      simpa [i0, iLast] using hb
    rw [hb', ← cornerMat_zero hn2 b]
  refine CFSG.GroupTheory.map_le_of_isPerfect_of_forall_odd_order
    (midBlock hn2) (Subgroup.normalizer (T : Set (SLn n K))) ?_ A
  intro B hBodd
  have hcomm : midBlock hn2 B * u = u * midBlock hn2 B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, huform]
    exact hcomm_of B
  have hBodd' : Odd (orderOf (midBlock hn2 B)) :=
    Odd.of_dvd_nat hBodd (orderOf_map_dvd (midBlock hn2) B)
  exact hwti u huT hu1 (midBlock hn2 B) hcomm hBodd'

private lemma exists_corner_and_G0
    (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K)
    {T : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hTU : T ≤ unitriangular n K)
    (hB : upperTriangular n K ≤ Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin n) K)))
    (hwti : ∀ t ∈ T, t ≠ 1 → ∀ y : SpecialLinearGroup (Fin n) K, y * t = t * y →
      Odd (orderOf y) → y ∈ Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin n) K))) :
    T = ⊥ ∨ ∃ z : SpecialLinearGroup (Fin n) K, z ∈ T ∧ ∃ c : K, c ≠ 0 ∧
      (z : Matrix (Fin n) (Fin n) K) =
        1 + Matrix.single ⟨0, by omega⟩ ⟨n - 1, by omega⟩ c ∧
      (∀ A : SpecialLinearGroup (Fin (n - 2)) K,
        midBlock (show 2 ≤ n by omega) A ∈
          Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin n) K))) := by
  by_cases hbot : T = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨u, huT, hu1, b, hb0, hb⟩ := exists_central_corner hn hTU hB hbot
    exact ⟨u, huT, b, hb0, hb,
      midBlock_mem_normalizer_of_perfect hn hq huT hu1 hb hwti⟩

private lemma Avec_smul (hn : 2 ≤ n) (c : K) (b : Fin (n - 2) → K) :
    Avec hn (c • b) = c • Avec hn b := by
  ext i j
  by_cases h : j = cL hn <;> simp [Avec, h]

private lemma Bvec_smul (hn : 2 ≤ n) (c : K) (a : Fin (n - 2) → K) :
    Bvec hn (c • a) = c • Bvec hn a := by
  ext i j
  by_cases h : i = c0 hn <;> simp [Bvec, h]

private lemma diagFull_mem_upperTriangular (hn : 2 ≤ n) (ν : K) (hν : ν ≠ 0) :
    (⟨diagFull hn ν, det_diagFull hn ν hν⟩ : SLn n K) ∈ upperTriangular n K := by
  change ∀ i j : Fin n, j < i → diagFull hn ν i j = 0
  intro i j hji
  let e := CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)
  have hdiag : (diagFull hn ν).IsDiag := by
    rw [diagFull, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
    refine Matrix.IsDiag.submatrix ?_ e.symm.injective
    rw [smul_one_eq_diagonal, outerDiag, Matrix.fromBlocks_diagonal]
    exact Matrix.isDiag_diagonal _
  exact hdiag (ne_of_gt hji)

private lemma diagFull_conj (hn : 2 ≤ n) (ν : K) (hν : ν ≠ 0)
    (a b : Fin (n - 2) → K) (c : K) :
    diagFull hn ν * cornerMat hn a b c * (diagFull hn ν)⁻¹ =
      cornerMat hn (((ν⁻¹) ^ n) • a) b (((ν⁻¹) ^ n) * c) := by
  let α : K := (ν ^ (n - 1))⁻¹
  let γ : K := (ν⁻¹) ^ n
  let e := CFSG.Timmesfeld.ARS.Linear.embEquiv (midEmb hn)
  have hα : α ≠ 0 := by
    dsimp only [α]
    exact inv_ne_zero (pow_ne_zero _ hν)
  have hγ : ν⁻¹ * α = γ := by
    dsimp only [α, γ]
    rw [← inv_pow, mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hγ' : α * ν⁻¹ = γ := by rw [mul_comm, hγ]
  have hA1 : (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)) * (ν⁻¹ • 1) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hν,
      one_smul]
  have hDinv : (Matrix.fromBlocks (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
        (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
        (outerDiag hn α ν))⁻¹ =
      Matrix.fromBlocks (ν⁻¹ • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
        (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
        (outerDiag hn α ν)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.fromBlocks_multiply, hA1, outerDiag_mul_inv hn α ν hα hν]
    simp [Matrix.fromBlocks_one]
  have h12 : (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)) * Avec hn b *
      (outerDiag hn α ν)⁻¹ = Avec hn b := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      Avec_mul_outerDiag_inv hn α ν hα hν, ← Avec_smul]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ hν, one_smul]
  have h21 : outerDiag hn α ν * Bvec hn a *
      (ν⁻¹ • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)) = Bvec hn (γ • a) := by
    rw [outerDiag_mul_Bvec, Matrix.mul_smul, Matrix.mul_one, ← Bvec_smul]
    congr 1
    rw [smul_smul, hγ]
  have h22 : outerDiag hn α ν * Dvec hn c * (outerDiag hn α ν)⁻¹ = Dvec hn (γ * c) := by
    rw [outerDiag_mul_Dvec_mul_inv hn α ν hα hν, hγ']
  have hblock : Matrix.fromBlocks (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
        (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
        (outerDiag hn α ν) *
      Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
        (Avec hn b) (Bvec hn a) (Dvec hn c) *
      (Matrix.fromBlocks (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
        (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
        (outerDiag hn α ν))⁻¹ =
      Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
        (Avec hn b) (Bvec hn (γ • a)) (Dvec hn (γ * c)) := by
    rw [hDinv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul, hA1, h12, h21, h22]
  calc
    diagFull hn ν * cornerMat hn a b c * (diagFull hn ν)⁻¹
        = Matrix.reindexAlgEquiv K K e
            (Matrix.fromBlocks (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
              (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
              (outerDiag hn α ν) *
            Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
              (Avec hn b) (Bvec hn a) (Dvec hn c) *
            (Matrix.fromBlocks (ν • (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K))
              (0 : Matrix (Fin (n - 2)) (C hn) K) (0 : Matrix (C hn) (Fin (n - 2)) K)
              (outerDiag hn α ν))⁻¹) := by
          simp [diagFull, cornerMat, e, α, γ, map_mul, map_inv]
    _ = Matrix.reindexAlgEquiv K K e
          (Matrix.fromBlocks (1 : Matrix (Fin (n - 2)) (Fin (n - 2)) K)
            (Avec hn b) (Bvec hn (γ • a)) (Dvec hn (γ * c))) := by
          rw [hblock]
    _ = cornerMat hn (γ • a) b (γ * c) := by
          simp [cornerMat, e]

private lemma cornerMat_row_eq_one_add_vecMulVec (hn : 2 ≤ n) (a : Fin (n - 2) → K) (c : K) :
    cornerMat hn a 0 c =
      1 + Matrix.vecMulVec (Pi.single (i0 hn) 1)
        (fun j => if j = i0 hn then 0 else cornerMat hn a 0 c (i0 hn) j) := by
  have h0l : i0 hn ≠ iLast hn := (i0_lt_iLast hn).ne
  have hl0 : iLast hn ≠ i0 hn := (i0_lt_iLast hn).ne'
  ext i j
  rw [Matrix.add_apply, Matrix.vecMulVec_apply]
  rcases eq_zero_or_eq_last_or_mid hn i with rfl | rfl | ⟨i', rfl⟩
  · rcases eq_zero_or_eq_last_or_mid hn j with rfl | rfl | ⟨j', rfl⟩
    · simp [cornerMat_apply_i0_i0]
    · simp [cornerMat_apply_i0_iLast, h0l, hl0]
    · have hi : i0 hn ≠ midEmb hn j' := i0_ne_midEmb hn j'
      have hi' : midEmb hn j' ≠ i0 hn := hi.symm
      simp [cornerMat_apply_i0_mid, hi, hi']
  · rcases eq_zero_or_eq_last_or_mid hn j with rfl | rfl | ⟨j', rfl⟩
    · simp [cornerMat_apply_iLast_i0, hl0]
    · simp [cornerMat_apply_iLast_iLast, hl0]
    · have hm : iLast hn ≠ midEmb hn j' := (midEmb_ne_iLast hn j').symm
      simp [cornerMat_apply_iLast_mid, hl0, hm]
  · rcases eq_zero_or_eq_last_or_mid hn j with rfl | rfl | ⟨j', rfl⟩
    · have hm : midEmb hn i' ≠ i0 hn := (i0_ne_midEmb hn i').symm
      simp [cornerMat_apply_mid_i0, hm]
    · have hm : midEmb hn i' ≠ i0 hn := (i0_ne_midEmb hn i').symm
      have hml : midEmb hn i' ≠ iLast hn := midEmb_ne_iLast hn i'
      simp [cornerMat_apply_mid_iLast, hm, hml]
    · rw [cornerMat_apply_mid_mid, Matrix.one_apply,
        Pi.single_eq_of_ne ((i0_ne_midEmb hn i').symm)]
      simp only [zero_mul, add_zero]
      by_cases h : i' = j'
      · subst h
        simp [Matrix.one_apply]
      · have h' : midEmb hn i' ≠ midEmb hn j' := fun hh => h ((midEmb hn).injective hh)
        simp [Matrix.one_apply, h, h']

private lemma cornerMat_col_eq_one_add_vecMulVec (hn : 2 ≤ n) (b : Fin (n - 2) → K) (c : K) :
    cornerMat hn 0 b c =
      1 + Matrix.vecMulVec
        (fun i => if i = iLast hn then 0 else cornerMat hn 0 b c i (iLast hn))
        (Pi.single (iLast hn) 1) := by
  have h0l : i0 hn ≠ iLast hn := (i0_lt_iLast hn).ne
  have hl0 : iLast hn ≠ i0 hn := (i0_lt_iLast hn).ne'
  ext i j
  rw [Matrix.add_apply, Matrix.vecMulVec_apply]
  rcases eq_zero_or_eq_last_or_mid hn j with rfl | rfl | ⟨j', rfl⟩
  · rcases eq_zero_or_eq_last_or_mid hn i with rfl | rfl | ⟨i', rfl⟩
    · simp [cornerMat_apply_i0_i0, hl0]
    · simp [cornerMat_apply_iLast_i0, hl0]
    · have hm : midEmb hn i' ≠ i0 hn := (i0_ne_midEmb hn i').symm
      simp [cornerMat_apply_mid_i0, hl0, hm]
  · rcases eq_zero_or_eq_last_or_mid hn i with rfl | rfl | ⟨i', rfl⟩
    · simp [cornerMat_apply_i0_iLast, h0l]
    · simp [cornerMat_apply_iLast_iLast]
    · have hml : midEmb hn i' ≠ iLast hn := midEmb_ne_iLast hn i'
      simp [cornerMat_apply_mid_iLast, hml]
  · rcases eq_zero_or_eq_last_or_mid hn i with rfl | rfl | ⟨i', rfl⟩
    · have hm : i0 hn ≠ midEmb hn j' := i0_ne_midEmb hn j'
      have hml : midEmb hn j' ≠ iLast hn := midEmb_ne_iLast hn j'
      simp [cornerMat_apply_i0_mid, hm, hml]
    · have hml : midEmb hn j' ≠ iLast hn := midEmb_ne_iLast hn j'
      simp [cornerMat_apply_iLast_mid, hml, hml.symm]
    · rw [cornerMat_apply_mid_mid, Matrix.one_apply,
        Pi.single_eq_of_ne (midEmb_ne_iLast hn j')]
      simp only [mul_zero, add_zero]
      by_cases h : i' = j'
      · subst h
        simp [Matrix.one_apply]
      · have h' : midEmb hn i' ≠ midEmb hn j' := fun hh => h ((midEmb hn).injective hh)
        simp [Matrix.one_apply, h, h']

private lemma exists_inv_pow_four_ne_one (hK : 4 ≤ Nat.card K) :
    ∃ ν : K, ν ≠ 0 ∧ (ν⁻¹) ^ 4 ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : 2 < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    omega
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, show ({0, 1} : Finset K).card = 2 by simp]
    omega
  obtain ⟨ν, -, hνmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hν' : ν ≠ 0 ∧ ν ≠ 1 := by simpa using hνmem
  obtain ⟨hν0, hν1⟩ := hν'
  have hγne : (ν⁻¹) ^ 4 ≠ 1 := by
    intro hγ
    have h0 : (ν⁻¹ - 1) ^ 4 = 0 := by
      have h := sub_pow_char_pow (p := 2) (n := 2) (x := ν⁻¹) (y := (1 : K))
      norm_num at h
      rw [h]
      have hγ' : (ν ^ 4)⁻¹ = 1 := by
        rw [← inv_pow]
        exact hγ
      rw [hγ', sub_self]
    have hνinv : ν⁻¹ = 1 := by
      have := (pow_eq_zero_iff (n := 4) (by norm_num)).mp h0
      exact sub_eq_zero.mp this
    exact hν1 (inv_eq_one.mp hνinv)
  exact ⟨ν, hν0, hγne⟩

private lemma exists_pure_row_conj_diag
    (hn4 : n = 4) {T : Subgroup (SLn n K)}
    (hB : upperTriangular n K ≤ Subgroup.normalizer (T : Set (SLn n K)))
    {x : SLn n K} (hxT : x ∈ T)
    {a b : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) a b c)
    (ha : a ≠ 0) {ν : K} (hν0 : ν ≠ 0)
    (hγne : (ν⁻¹) ^ 4 ≠ 1) :
    ∃ x₁ ∈ T, ∃ a₁ : Fin (n - 2) → K, ∃ c₁ : K,
      a₁ ≠ 0 ∧ (x₁ : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) a₁ 0 c₁ := by
  subst n
  classical
  let γ : K := (ν⁻¹) ^ 4
  have hγne' : γ ≠ 1 := hγne
  let hn2 : 2 ≤ 4 := by omega
  let dSL : SpecialLinearGroup (Fin 4) K := ⟨diagFull hn2 ν, det_diagFull hn2 ν hν0⟩
  have hdB : dSL ∈ upperTriangular 4 K := diagFull_mem_upperTriangular hn2 ν hν0
  have hdN : dSL ∈ Subgroup.normalizer (T : Set (SLn 4 K)) := hB hdB
  have hconj : dSL * x * dSL⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hdN x).mp hxT
  let x₁ : SpecialLinearGroup (Fin 4) K := dSL * x * dSL⁻¹ * x
  have hx₁T : x₁ ∈ T := T.mul_mem hconj hxT
  have hcoe_inv : ((dSL⁻¹ : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = (diagFull hn2 ν)⁻¹ := by
    apply Eq.symm
    apply Matrix.inv_eq_right_inv
    change (dSL : Matrix (Fin 4) (Fin 4) K) *
      ((dSL⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hx₁ : (x₁ : Matrix (Fin 4) (Fin 4) K) =
      cornerMat hn2 ((γ + 1) • a) 0 (γ * c + c + (γ • a) ⬝ᵥ b) := by
    change ((dSL * x * dSL⁻¹ * x : SpecialLinearGroup (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = _
    rw [Matrix.SpecialLinearGroup.coe_mul]
    have hconj_mat : ((dSL * x * dSL⁻¹ : SpecialLinearGroup (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) =
        diagFull hn2 ν * (x : Matrix (Fin 4) (Fin 4) K) * (diagFull hn2 ν)⁻¹ := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcoe_inv]
    rw [hconj_mat, hx, diagFull_conj hn2 ν hν0 a b c, cornerMat_mul]
    rw [show (γ • a) + a = (γ + 1) • a by
      ext k
      simp only [Pi.add_apply, Pi.smul_apply]
      ring,
      show b + b = 0 by
      ext k
      exact CharTwo.add_self_eq_zero (b k)]
  have ha₁ : (γ + 1) • a ≠ 0 := by
    have hγ1 : γ + 1 ≠ 0 := by
      intro h
      exact hγne' (CharTwo.add_eq_zero.mp h)
    intro h
    rcases (smul_eq_zero.mp h) with h | h
    · exact hγ1 h
    · exact ha h
  exact ⟨x₁, hx₁T, (γ + 1) • a, γ * c + c + (γ • a) ⬝ᵥ b, ha₁, hx₁⟩

private lemma exists_pure_row_of_n_eq_four
    (hn4 : n = 4) (hq4 : 4 ≤ Nat.card K)
    {T : Subgroup (SLn n K)}
    (hB : upperTriangular n K ≤ Subgroup.normalizer (T : Set (SLn n K)))
    {x : SLn n K} (hxT : x ∈ T)
    {a b : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) a b c)
    (ha : a ≠ 0) :
    ∃ x₁ ∈ T, ∃ a₁ : Fin (n - 2) → K, ∃ c₁ : K,
      a₁ ≠ 0 ∧ (x₁ : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) a₁ 0 c₁ := by
  obtain ⟨ν, hν0, hγne⟩ := exists_inv_pow_four_ne_one hq4
  exact exists_pure_row_conj_diag hn4 hB hxT hx ha hν0 hγne

private lemma exists_pure_row_of_five_le
    (hn5 : 5 ≤ n)
    {T : Subgroup (SLn n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock (show 2 ≤ n by omega) A ∈ Subgroup.normalizer (T : Set (SLn n K)))
    {x : SLn n K} (hxT : x ∈ T)
    {a b : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) a b c)
    (ha : a ≠ 0) :
    ∃ x₁ ∈ T, ∃ a₁ : Fin (n - 2) → K, ∃ c₁ : K,
      a₁ ≠ 0 ∧ (x₁ : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) a₁ 0 c₁ := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hcard : 1 < Fintype.card (Fin (n - 2)) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  have hlt : ({i, j} : Finset (Fin (n - 2))).card <
      (Finset.univ : Finset (Fin (n - 2))).card := by
    have hle : ({i, j} : Finset (Fin (n - 2))).card ≤ 2 := by
      simpa using Finset.card_insert_le i ({j} : Finset (Fin (n - 2)))
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hki : k ≠ i := by
    intro h
    exact hk (by simp [h])
  have hkj : k ≠ j := by
    intro h
    exact hk (by simp [h])
  obtain ⟨y, hyT, c₁, hy⟩ := exists_commutator_params (by omega : 4 ≤ n)
    (show 2 ≤ n by omega) hT hG0 hxT hx hji.symm (1 : K)
  have hy' : (y : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) (Pi.single j (a i)) (Pi.single i (b j)) c₁ := by
    simpa using hy
  obtain ⟨z, hzT, c₂, hz⟩ := exists_commutator_params (by omega : 4 ≤ n)
    (show 2 ≤ n by omega) hT hG0 hyT hy' hkj.symm (1 : K)
  have hz' : (z : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) (Pi.single k (a i)) 0 c₂ := by
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne hki, Pi.single_zero] using hz
  refine ⟨z, hzT, Pi.single k (a i), c₂, ?_, hz'⟩
  intro h
  apply hi
  have := congrFun h k
  simpa using this

private lemma exists_unit_row_of_exists_row
    (hn : 4 ≤ n)
    {T : Subgroup (SLn n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock (show 2 ≤ n by omega) A ∈ Subgroup.normalizer (T : Set (SLn n K)))
    {x : SLn n K} (hxT : x ∈ T)
    {a : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) a 0 c)
    (ha : a ≠ 0) :
    ∀ l : Fin (n - 2), ∃ y ∈ T, ∃ c' : K,
      (y : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) (Pi.single l 1) 0 c' := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  intro l
  by_cases hli : l = i
  · subst l
    have hcard : 1 < Fintype.card (Fin (n - 2)) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    obtain ⟨y, hyT, c₁, hy⟩ := exists_commutator_params hn (show 2 ≤ n by omega)
      hT hG0 hxT hx hji.symm (a i)⁻¹
    have hy' : (y : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) (Pi.single j 1) 0 c₁ := by
      simpa [inv_mul_cancel₀ hi, Pi.single_zero] using hy
    obtain ⟨z, hzT, c₂, hz⟩ := exists_commutator_params hn (show 2 ≤ n by omega)
      hT hG0 hyT hy' hji (1 : K)
    refine ⟨z, hzT, c₂, ?_⟩
    simpa [Pi.single_eq_same, Pi.single_zero] using hz
  · obtain ⟨y, hyT, c₁, hy⟩ := exists_commutator_params hn (show 2 ≤ n by omega)
      hT hG0 hxT hx (Ne.symm hli) (a i)⁻¹
    refine ⟨y, hyT, c₁, ?_⟩
    simpa [inv_mul_cancel₀ hi, Pi.single_zero] using hy

private lemma exists_pure_row
    (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K)
    {T : Subgroup (SLn n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock (show 2 ≤ n by omega) A ∈ Subgroup.normalizer (T : Set (SLn n K)))
    (hB : upperTriangular n K ≤ Subgroup.normalizer (T : Set (SLn n K)))
    {x : SLn n K} (hxT : x ∈ T)
    {a b : Fin (n - 2) → K} {c : K}
    (hx : (x : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) a b c)
    (ha : a ≠ 0) :
    ∃ x₁ ∈ T, ∃ a₁ : Fin (n - 2) → K, ∃ c₁ : K,
      a₁ ≠ 0 ∧ (x₁ : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) a₁ 0 c₁ := by
  by_cases hn4 : n = 4
  · exact exists_pure_row_of_n_eq_four hn4 (hq hn4) hB hxT hx ha
  · exact exists_pure_row_of_five_le (by omega) hT hG0 hxT hx ha

private lemma le_tvCenterSL_of_exists_row
    (hn : 4 ≤ n)
    {T : Subgroup (SLn n K)} (hT : Assembly.IsElemAbelian 2 T)
    (hG0 : ∀ A : SpecialLinearGroup (Fin (n - 2)) K,
      midBlock (show 2 ≤ n by omega) A ∈ Subgroup.normalizer (T : Set (SLn n K)))
    (hcorner : ∀ x ∈ T, ∃ a b : Fin (n - 2) → K, ∃ c : K,
      (x : Matrix (Fin n) (Fin n) K) = cornerMat (show 2 ≤ n by omega) a b c)
    {x₁ : SLn n K} (hx₁T : x₁ ∈ T)
    {a₁ : Fin (n - 2) → K} {c₁ : K}
    (hx₁ : (x₁ : Matrix (Fin n) (Fin n) K) =
      cornerMat (show 2 ≤ n by omega) a₁ 0 c₁)
    (ha₁ : a₁ ≠ 0) :
    T ≤ tvCenterSL (Pi.single (i0 (show 2 ≤ n by omega)) 1) := by
  have hunit := exists_unit_row_of_exists_row hn hT hG0 hx₁T hx₁ ha₁
  intro x' hx'T
  obtain ⟨a₂, b₂, c₂, hx'⟩ := hcorner x' hx'T
  have hb₂ : b₂ = 0 := by
    funext l
    obtain ⟨y, hyT, c', hy⟩ := hunit l
    have hxy : ((x' * y : SLn n K) : Matrix (Fin n) (Fin n) K) =
        cornerMat (show 2 ≤ n by omega) (a₂ + Pi.single l 1) (b₂ + 0)
          (c₂ + c' + a₂ ⬝ᵥ 0) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hx', hy, cornerMat_mul]
    have h1 : a₂ ⬝ᵥ b₂ = 0 := cornerMat_dot_eq_zero hn hT hx'T hx'
    have h2 : (a₂ + Pi.single l 1) ⬝ᵥ (b₂ + 0) = 0 :=
      cornerMat_dot_eq_zero hn hT (T.mul_mem hx'T hyT) hxy
    have h2' : (a₂ + Pi.single l 1) ⬝ᵥ b₂ = 0 := by simpa using h2
    have h3 : Pi.single l 1 ⬝ᵥ b₂ = 0 := by
      rw [add_dotProduct, h1, zero_add] at h2'
      exact h2'
    simpa using h3
  subst b₂
  rw [mem_tvCenterSL]
  let w : Fin n → K := fun j =>
    if j = i0 (show 2 ≤ n by omega) then 0
    else cornerMat (show 2 ≤ n by omega) a₂ 0 c₂ (i0 (show 2 ≤ n by omega)) j
  refine ⟨w, ?_, ?_⟩
  · rw [dotProduct_single_one]
    simp [w]
  · simpa [w] using hx'.trans
      (cornerMat_row_eq_one_add_vecMulVec (show 2 ≤ n by omega) a₂ c₂)

private lemma le_tvAxisSL_of_forall_row_zero
    (hn : 4 ≤ n)
    {T : Subgroup (SLn n K)}
    (hcorner : ∀ x ∈ T, ∃ a b : Fin (n - 2) → K, ∃ c : K,
      (x : Matrix (Fin n) (Fin n) K) = cornerMat (show 2 ≤ n by omega) a b c)
    (hzero : ∀ x ∈ T, ∀ (a b : Fin (n - 2) → K) (c : K),
      (x : Matrix (Fin n) (Fin n) K) = cornerMat (show 2 ≤ n by omega) a b c → a = 0) :
    T ≤ tvAxisSL (Pi.single (iLast (show 2 ≤ n by omega)) 1) := by
  intro x' hx'T
  obtain ⟨a₂, b₂, c₂, hx'⟩ := hcorner x' hx'T
  have ha₂ : a₂ = 0 := hzero x' hx'T a₂ b₂ c₂ hx'
  subst a₂
  rw [mem_tvAxisSL]
  let v : Fin n → K := fun i =>
    if i = iLast (show 2 ≤ n by omega) then 0
    else cornerMat (show 2 ≤ n by omega) 0 b₂ c₂ i (iLast (show 2 ≤ n by omega))
  refine ⟨v, ?_, ?_⟩
  · rw [single_one_dotProduct]
    simp [v]
  · simpa [v] using hx'.trans
      (cornerMat_col_eq_one_add_vecMulVec (show 2 ≤ n by omega) b₂ c₂)

theorem le_tvCenterSL_or_le_tvAxisSL
    (hn : 4 ≤ n) (hq : n = 4 → 4 ≤ Nat.card K)
    {T : Subgroup (SpecialLinearGroup (Fin n) K)} (hT : Assembly.IsElemAbelian 2 T)
    (hTU : T ≤ unitriangular n K)
    (hB : upperTriangular n K ≤ Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin n) K)))
    (hwti : ∀ t ∈ T, t ≠ 1 → ∀ y : SpecialLinearGroup (Fin n) K, y * t = t * y →
      Odd (orderOf y) → y ∈ Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin n) K))) :
    T ≤ tvCenterSL
        (Pi.single (⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) hn⟩ : Fin n) 1) ∨
      T ≤ tvAxisSL
        (Pi.single (⟨n - 1, Nat.sub_one_lt_of_lt
          (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) hn)⟩ : Fin n) 1) := by
  rcases exists_corner_and_G0 hn hq hTU hB hwti with hbot | ⟨z, hzT, cz, hcz, hz, hG0⟩
  · left
    rw [hbot]
    exact bot_le
  · have hcorner := exists_corner_of_mem hn hTU hG0
    by_cases hrow : ∃ x ∈ T, ∃ a b : Fin (n - 2) → K, ∃ c : K,
        (x : Matrix (Fin n) (Fin n) K) =
          cornerMat (show 2 ≤ n by omega) a b c ∧ a ≠ 0
    · left
      obtain ⟨x₀, hx₀T, a₀, b₀, c₀, hx₀, ha₀⟩ := hrow
      obtain ⟨x₁, hx₁T, a₁, c₁, ha₁, hx₁⟩ :=
        exists_pure_row hn hq hT hG0 hB hx₀T hx₀ ha₀
      exact le_tvCenterSL_of_exists_row hn hT hG0 hcorner hx₁T hx₁ ha₁
    · right
      refine le_tvAxisSL_of_forall_row_zero hn hcorner ?_
      intro x' hx'T a₂ b₂ c₂ hx'
      by_contra ha₂
      exact hrow ⟨x', hx'T, a₂, b₂, c₂, hx', ha₂⟩

theorem exists_invariant_of_le_tvCenterSL
    (hn : 3 ≤ n) {T : Subgroup (SpecialLinearGroup (Fin n) K)} {c : Fin n → K}
    (hTc : T ≤ tvCenterSL c) (hc : c ≠ 0) (g : SpecialLinearGroup (Fin n) K) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x ∈ T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T, ∀ w ∈ W,
        (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  let p : Submodule K (Fin n → K) := Submodule.span K {c}
  have hp : Module.finrank K p = 1 := by
    dsimp [p]
    exact finrank_span_singleton hc
  have hcent : ∀ t ∈ T.map (Matrix.SpecialLinearGroup.toGL),
      LinearMap.range (CFSG.LinearAlgebra.shiftEnd t) ≤ p := by
    intro t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨s, hsT, rfl⟩ := ht
    obtain ⟨a, hac, hs⟩ := hTc hsT
    rintro _ ⟨u, rfl⟩
    change ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ u ∈ p
    rw [show ((s : Matrix (Fin n) (Fin n) K) - 1) = Matrix.vecMulVec c a by
      rw [hs]
      abel, Matrix.vecMulVec_mulVec]
    simpa [op_smul_eq_smul] using
      Submodule.smul_mem p (a ⬝ᵥ u) (Submodule.subset_span (Set.mem_singleton c))
  obtain ⟨W, hWbot, hWtop, hWinv⟩ :=
    CFSG.LinearAlgebra.exists_invariant_of_common_centre (K := K) (n := n) hn
      (T.map (Matrix.SpecialLinearGroup.toGL)) (Matrix.SpecialLinearGroup.toGL g) hp hcent
  refine ⟨W, hWbot, hWtop, ?_⟩
  intro x hx w hw
  have hx' : Matrix.SpecialLinearGroup.toGL x ∈
      T.map (Matrix.SpecialLinearGroup.toGL) ⊔
        CFSG.CGT.Timmesfeld75.conjSubgroup (Matrix.SpecialLinearGroup.toGL g)
          (T.map (Matrix.SpecialLinearGroup.toGL)) := by
    rw [← map_conjSubgroup, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem _ hx
  simpa using hWinv _ hx' w hw

theorem exists_invariant_of_le_tvAxisSL
    (hn : 3 ≤ n) {T : Subgroup (SpecialLinearGroup (Fin n) K)} {a : Fin n → K}
    (hTa : T ≤ tvAxisSL a) (ha : a ≠ 0) (g : SpecialLinearGroup (Fin n) K) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x ∈ T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T, ∀ w ∈ W,
        (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  let l : Submodule K (Fin n → K) := LinearMap.ker (dotLin a)
  have hl : Module.finrank K l = n - 1 := by
    have hr : LinearMap.range (dotLin a) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      obtain ⟨x, hx⟩ := CFSG.CGT.Timmesfeld75.exists_dot_eq_one_K (K := K) (m := n) ha
      exact ⟨c • x, by simp [dotLin_apply, hx]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (dotLin a)
    rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    dsimp [l]
    omega
  have haxis : ∀ t ∈ T.map (Matrix.SpecialLinearGroup.toGL),
      l ≤ LinearMap.ker (CFSG.LinearAlgebra.shiftEnd t) := by
    intro t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨s, hsT, rfl⟩ := ht
    obtain ⟨b, hba, hs⟩ := hTa hsT
    intro u hu
    rw [LinearMap.mem_ker]
    change ((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ u = 0
    rw [show ((s : Matrix (Fin n) (Fin n) K) - 1) = Matrix.vecMulVec b a by
      rw [hs]
      abel, Matrix.vecMulVec_mulVec]
    have hau : a ⬝ᵥ u = 0 := by
      have := hu
      rw [LinearMap.mem_ker, dotLin_apply] at this
      exact this
    rw [hau, op_smul_eq_smul, zero_smul]
  obtain ⟨W, hWbot, hWtop, hWinv⟩ :=
    CFSG.LinearAlgebra.exists_invariant_of_common_axis (K := K) (n := n) hn
      (T.map (Matrix.SpecialLinearGroup.toGL)) (Matrix.SpecialLinearGroup.toGL g) hl haxis
  refine ⟨W, hWbot, hWtop, ?_⟩
  intro x hx w hw
  have hx' : Matrix.SpecialLinearGroup.toGL x ∈
      T.map (Matrix.SpecialLinearGroup.toGL) ⊔
        CFSG.CGT.Timmesfeld75.conjSubgroup (Matrix.SpecialLinearGroup.toGL g)
          (T.map (Matrix.SpecialLinearGroup.toGL)) := by
    rw [← map_conjSubgroup, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem _ hx
  simpa using hWinv _ hx' w hw

end CFSG.RankThree.GF2n.Tim81

end
