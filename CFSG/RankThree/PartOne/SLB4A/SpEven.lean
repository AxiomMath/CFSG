module

public import CFSG.RankThree.PartOne.SLB4A.Unip

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

section Sp

variable {K : Type} [Field K] {r : ℕ}

def spS (hr : 3 ≤ r) : Fin 5 → Matrix (Fin r) (Fin r) K := fun k =>
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  let c : Fin r := ⟨2, by omega⟩
  match k with
  | 0 => Matrix.single a a 1
  | 1 => Matrix.single b b 1
  | 2 => Matrix.single c c 1
  | 3 => Matrix.single a b 1 + Matrix.single b a 1
  | 4 => Matrix.single a c 1 + Matrix.single c a 1

def spX (hr : 3 ≤ r) (k : Fin 5) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.fromBlocks 0 (spS hr k) 0 0

theorem spX_mul (hr : 3 ≤ r) (k l : Fin 5) : spX hr k * spX hr l = (0 : Matrix _ _ K) := by
  simp [spX, Matrix.fromBlocks_multiply]

theorem spS_symm (hr : 3 ≤ r) (k : Fin 5) : (spS hr k : Matrix (Fin r) (Fin r) K)ᵀ = spS hr k := by
  fin_cases k <;> simp [spS, Matrix.transpose_single, add_comm]

theorem spX_ind [CharP K 2] (hr : 3 ≤ r) (v : V2 5)
    (h : ∃ c : K, Xsum (spX (K := K) hr) v = Matrix.scalar (Fin r ⊕ Fin r) c) : v = 1 := by
  obtain ⟨c, hc⟩ := h
  have key : ∀ i j : Fin r, (Xsum (spX (K := K) hr) v : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
      (Sum.inl i) (Sum.inr j) = 0 := fun i j => by
    rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by simp)]
  have e0 := key ⟨0, by omega⟩ ⟨0, by omega⟩
  have e1 := key ⟨1, by omega⟩ ⟨1, by omega⟩
  have e2 := key ⟨2, by omega⟩ ⟨2, by omega⟩
  have e3 := key ⟨0, by omega⟩ ⟨1, by omega⟩
  have e4 := key ⟨0, by omega⟩ ⟨2, by omega⟩
  simp only [Xsum, Matrix.sum_apply, Matrix.smul_apply, spX, Matrix.fromBlocks_apply₁₂, Fin.sum_univ_five] at e0 e1 e2 e3 e4
  simp [spS, Fin.ext_iff] at e0 e1 e2 e3 e4
  have one_ne : (1 : K) ≠ 0 := one_ne_zero
  funext k
  fin_cases k
  · exact cC2_eq_zero _ e0 one_ne
  · exact cC2_eq_zero _ e1 one_ne
  · exact cC2_eq_zero _ e2 one_ne
  · exact cC2_eq_zero _ e3 one_ne
  · exact cC2_eq_zero _ e4 one_ne

theorem spX_mem [CharP K 2] (hr : 3 ≤ r) (k : Fin 5) :
    uniMat (spX_mul (K := K) hr) (Pi.mulSingle k c2gen) ∈ StatedSp r K := by
  refine Subgroup.subset_closure ?_
  show ((uniMat (spX_mul (K := K) hr) (Pi.mulSingle k c2gen) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      ((uniMat (spX_mul (K := K) hr) (Pi.mulSingle k c2gen) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Matrix.fromBlocks 0 1 (-1) 0
  rw [coe_uniMat, Xsum_mulSingle]
  have e : (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + spX hr k =
      Matrix.fromBlocks 1 (spS hr k) 0 1 := by
    rw [spX, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp
  rw [e]
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, spS_symm]

theorem exists_two_pow_five_psp_even [CharP K 2] (hr : 3 ≤ r) :
    ∃ U : Subgroup (StatedProj (StatedSp r K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 :=
  exists_two_pow_five_unip (spX_mul hr) (fun v h => spX_ind hr v h) _ (spX_mem hr)

end Sp

end CFSG.RankThree.PartOne.SLB4A
