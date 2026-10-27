module

public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.RankThree.Lattice

open Polynomial Matrix

variable {n : ℕ}

@[expose] def orbitMat (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (m : ℕ) :
    Matrix (Fin n) (Fin m) ℤ :=
  Matrix.of fun i j => ((w ^ (j : ℕ)) *ᵥ x) i

@[expose] def orbitLattice (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range fun j : ℕ => (w ^ j) *ᵥ x)

theorem orbitMat_col (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (m : ℕ) (j : Fin m) :
    (orbitMat w x m).col j = (w ^ (j : ℕ)) *ᵥ x :=
  rfl

theorem orbitMat_pow_mulVec (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (m j : ℕ) :
    orbitMat w ((w ^ j) *ᵥ x) m = w ^ j * orbitMat w x m := by
  ext i k
  have h1 : (w ^ (k : ℕ)) *ᵥ ((w ^ j) *ᵥ x) = (w ^ j) *ᵥ ((w ^ (k : ℕ)) *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_add, ← pow_add, add_comm]
  simp only [orbitMat, Matrix.of_apply, Matrix.mul_apply, h1]
  rfl

theorem det_orbitMat_pow_mulVec (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (j : ℕ) :
    (orbitMat w ((w ^ j) *ᵥ x) n).det = w.det ^ j * (orbitMat w x n).det := by
  rw [orbitMat_pow_mulVec, Matrix.det_mul, Matrix.det_pow]

theorem orbitMat_neg (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (m : ℕ) :
    orbitMat w (-x) m = -orbitMat w x m := by
  ext i k
  simp [orbitMat, Matrix.mulVec_neg]

theorem det_orbitMat_neg (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (orbitMat w (-x) n).det = (-1) ^ n * (orbitMat w x n).det := by
  rw [orbitMat_neg, Matrix.det_neg, Fintype.card_fin]

theorem pow_mulVec_mem_orbitLattice (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) (j : ℕ) :
    (w ^ j) *ᵥ x ∈ orbitLattice w x :=
  Submodule.subset_span ⟨j, rfl⟩

theorem aeval_mulVec_eq_orbitMat_mulVec (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    {q : ℤ[X]} {m : ℕ} (hq : q.natDegree < m) :
    (aeval w q) *ᵥ x = orbitMat w x m *ᵥ fun i : Fin m => q.coeff i := by
  rw [aeval_eq_sum_range' hq, Matrix.sum_mulVec, ← Fin.sum_univ_eq_sum_range]
  funext a
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, orbitMat,
    Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem orbitLattice_eq_span_of_monic (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    {p : ℤ[X]} (hp : p.Monic) {k : ℕ} (hk : p.natDegree = k) (h : (aeval w p) *ᵥ x = 0) :
    orbitLattice w x = Submodule.span ℤ (Set.range fun j : Fin k => (w ^ (j : ℕ)) *ᵥ x) := by
  set S := Submodule.span ℤ (Set.range fun j : Fin k => (w ^ (j : ℕ)) *ᵥ x) with hS
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨j, rfl⟩
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < k
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · push Not at hj
        have hrel : (w ^ k) *ᵥ x = -∑ i ∈ Finset.range k, p.coeff i • ((w ^ i) *ᵥ x) := by
          have h1 := h
          rw [hp.as_sum, hk, map_add, map_sum] at h1
          simp only [map_pow, aeval_X, aeval_C, map_mul, Matrix.add_mulVec, Matrix.sum_mulVec,
            Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, smul_mul_assoc, one_mul] at h1
          exact eq_neg_of_add_eq_zero_left h1
        have hj' : j = (j - k) + k := by omega
        have hwj : (w ^ j) *ᵥ x = -∑ i ∈ Finset.range k, p.coeff i • ((w ^ (j - k + i)) *ᵥ x) := by
          rw [hj', pow_add, ← Matrix.mulVec_mulVec, hrel, Matrix.mulVec_neg, Matrix.mulVec_sum,
            ← hj']
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add]
        change (w ^ j) *ᵥ x ∈ S
        rw [hwj]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
        have hi' : i < k := Finset.mem_range.1 hi
        exact ih _ (by omega)
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem charpoly_eq_of_cyclic (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) {p : ℤ[X]}
    (hp : p.Monic) (hn : p.natDegree = n) (h : (aeval w p) *ᵥ x = 0)
    (hdet : (orbitMat w x n).det ≠ 0) : w.charpoly = p := by
  set q := w.charpoly - p with hq
  have hcp : w.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hqdeg : q.natDegree < n ∨ q = 0 := by
    by_cases hq0 : q = 0
    · exact Or.inr hq0
    · left
      have hlt : q.degree < w.charpoly.degree := by
        apply Polynomial.degree_sub_lt_left
        · rw [Polynomial.degree_eq_natDegree (w.charpoly_monic.ne_zero),
            Polynomial.degree_eq_natDegree hp.ne_zero, hcp, hn]
        · exact w.charpoly_monic.ne_zero
        · rw [w.charpoly_monic.leadingCoeff, hp.leadingCoeff]
      rw [Polynomial.degree_eq_natDegree w.charpoly_monic.ne_zero, hcp] at hlt
      exact (Polynomial.natDegree_lt_iff_degree_lt hq0).2 hlt
  rcases hqdeg with hlt | h0
  · have hqx : (aeval w q) *ᵥ x = 0 := by
      rw [hq, map_sub, Matrix.aeval_self_charpoly, zero_sub, Matrix.neg_mulVec, h, neg_zero]
    rw [aeval_mulVec_eq_orbitMat_mulVec w x hlt] at hqx
    have hc := Matrix.eq_zero_of_mulVec_eq_zero hdet hqx
    have hq0 : q = 0 := by
      ext i
      by_cases hi : i < n
      · exact congrFun hc ⟨i, hi⟩
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact sub_eq_zero.1 hq0
  · exact sub_eq_zero.1 h0

theorem isBasis_iff_isUnit_det (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (LinearIndependent ℤ (fun j : Fin n => (w ^ (j : ℕ)) *ᵥ x) ∧
      Submodule.span ℤ (Set.range fun j : Fin n => (w ^ (j : ℕ)) *ᵥ x) = ⊤) ↔
      IsUnit (orbitMat w x n).det := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun ℤ (Fin n)), Module.Basis.det_apply]
  rfl

theorem orbitLattice_eq_span_of_charpoly (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    orbitLattice w x = Submodule.span ℤ (Set.range fun j : Fin n => (w ^ (j : ℕ)) *ᵥ x) :=
  orbitLattice_eq_span_of_monic w x w.charpoly_monic
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
    (by rw [Matrix.aeval_self_charpoly, Matrix.zero_mulVec])

theorem index_orbitLattice (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ)
    (hdet : (orbitMat w x n).det ≠ 0) :
    (orbitLattice w x).toAddSubgroup.index = (orbitMat w x n).det.natAbs := by
  have hli : LinearIndependent ℤ (fun j : Fin n => (w ^ (j : ℕ)) *ᵥ x) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hspan := orbitLattice_eq_span_of_charpoly w x
  have h := Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin n)) (orbitLattice w x)
    ((Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan.symm))
  have hcomp : ((↑) ∘ ((Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan.symm)) :
      Fin n → Fin n → ℤ) = fun j : Fin n => (w ^ (j : ℕ)) *ᵥ x := by
    funext j
    simp [Module.Basis.span_apply]
  rw [hcomp, Module.Basis.det_apply] at h
  rw [AddSubgroup.index]
  exact h.symm

end CFSG.RankThree.Lattice
