module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.Quasithin.B45Ln

open Matrix

section Rank

variable {k : Type*} [Field k]

theorem le_rank_of_submatrix {m n : Type*} [Fintype m] [Fintype n] {r : ℕ} (A : Matrix m n k)
    (ri : Fin r → m) (ci : Fin r → n) (Y : Matrix (Fin r) (Fin r) k)
    (h : A.submatrix ri ci * Y = 1) : r ≤ A.rank := by
  have h1 := rank_mul_le_left (A.submatrix ri ci) Y
  rw [h, rank_one, Fintype.card_fin] at h1
  exact h1.trans (rank_submatrix_le A ri ci)

@[expose] def stackMat {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) k) :
    Matrix (Fin m × Fin n) (Fin n) k :=
  Matrix.of fun p j => (M p.1 - 1) p.2 j

theorem stackMat_mulVec_apply {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (p : Fin m × Fin n) : (stackMat M *ᵥ v) p = (M p.1 *ᵥ v - v) p.2 := by
  have h : (stackMat M *ᵥ v) p = ((M p.1 - 1) *ᵥ v) p.2 := rfl
  rw [h, sub_mulVec, one_mulVec]

theorem stackMat_mulVec_eq_zero {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) : stackMat M *ᵥ v = 0 ↔ ∀ i, M i *ᵥ v = v := by
  constructor
  · intro h i
    funext a
    have h1 := congrFun h (i, a)
    rw [stackMat_mulVec_apply, Pi.zero_apply, Pi.sub_apply] at h1
    exact sub_eq_zero.mp h1
  · intro h
    funext p
    rw [stackMat_mulVec_apply, h p.1, sub_self, Pi.zero_apply, Pi.zero_apply]

@[expose] def fixedSpace {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) k) :
    Submodule k (Fin n → k) :=
  LinearMap.ker (stackMat M).mulVecLin

theorem mem_fixedSpace {m n : ℕ} {M : Fin m → Matrix (Fin n) (Fin n) k} {v : Fin n → k} :
    v ∈ fixedSpace M ↔ ∀ i, M i *ᵥ v = v := by
  rw [fixedSpace, LinearMap.mem_ker, Matrix.mulVecLin_apply, stackMat_mulVec_eq_zero]

theorem finrank_fixedSpace {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) k) :
    Module.finrank k (fixedSpace M) + (stackMat M).rank = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (stackMat M).mulVecLin
  rw [Module.finrank_fin_fun] at h
  rw [fixedSpace, Matrix.rank, add_comm]
  exact h

theorem finrank_fixedSpace_le {m n : ℕ} {M : Fin m → Matrix (Fin n) (Fin n) k} {r : ℕ}
    (hr : r ≤ (stackMat M).rank) : Module.finrank k (fixedSpace M) ≤ n - r := by
  have := finrank_fixedSpace M
  omega

theorem eq_smul_of_rank {m n : ℕ} {M : Fin m → Matrix (Fin n) (Fin n) k}
    (hr : n - 1 ≤ (stackMat M).rank) {y : Fin n → k} (hy0 : y ≠ 0) (hy : ∀ i, M i *ᵥ y = y)
    {v : Fin n → k} (hv : ∀ i, M i *ᵥ v = v) : ∃ c : k, v = c • y := by
  have hle := finrank_fixedSpace_le hr
  have hyS : Submodule.span k {y} ≤ fixedSpace M := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact mem_fixedSpace.mpr hy
  have h1 : Module.finrank k (Submodule.span k {y}) = 1 := finrank_span_singleton hy0
  have heq : Submodule.span k {y} = fixedSpace M := by
    refine Submodule.eq_of_le_of_finrank_le hyS ?_
    rw [h1]
    have : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (Subsingleton.elim y 0) hy0
      · exact h
    omega
  have hv' : v ∈ Submodule.span k {y} := heq ▸ mem_fixedSpace.mpr hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
  exact ⟨c, hc.symm⟩

theorem card_fixed_le [Finite k] {m n : ℕ} {M : Fin m → Matrix (Fin n) (Fin n) k} {r : ℕ}
    (hr : r ≤ (stackMat M).rank) :
    Nat.card {v : Fin n → k // ∀ i, M i *ᵥ v = v} ≤ Nat.card k ^ (n - r) := by
  have e : {v : Fin n → k // ∀ i, M i *ᵥ v = v} ≃ fixedSpace M :=
    Equiv.subtypeEquivRight fun v => mem_fixedSpace.symm
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k)]
  exact Nat.pow_le_pow_right Nat.card_pos (finrank_fixedSpace_le hr)

end Rank

section Coord

variable {G : Type*} [Group G] {k : Type*} [Field k] {W : Type*} [AddCommMonoid W]
  [Module k W] {n : ℕ}

@[expose] def coordRep (R : Representation k G W) (c : W →ₗ[k] (Fin n → k))
    (s : (Fin n → k) →ₗ[k] W) (hcs : ∀ v, c (s v) = v)
    (hsc : ∀ g h v, c (R g (s (c (R h (s v))))) = c (R g (R h (s v)))) :
    Representation k G (Fin n → k) where
  toFun g := c ∘ₗ R g ∘ₗ s
  map_one' := LinearMap.ext fun v => by
    change c (R 1 (s v)) = v
    rw [map_one, Module.End.one_apply, hcs]
  map_mul' g h := LinearMap.ext fun v => by
    change c (R (g * h) (s v)) = c (R g (s (c (R h (s v)))))
    rw [map_mul, Module.End.mul_apply, hsc]

end Coord

section Gen

variable {G : Type*} [Group G] {k : Type*} [Field k] {n : ℕ}

theorem orbitSpan_eq_top_of_mul (ρ : Representation k G (Fin n → k)) (x : Fin n → k)
    (v : Fin n → Fin n → k) (hv : ∀ i, v i ∈ SmithCurtis.orbitSpan ρ x)
    (Y : Matrix (Fin n) (Fin n) k) (hY : Matrix.of (fun a i => v i a) * Y = 1) :
    SmithCurtis.orbitSpan ρ x = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, (Y *ᵥ w) i • v i := by
    have h1 : (Matrix.of (fun a i => v i a) * Y) *ᵥ w = w := by rw [hY, one_mulVec]
    rw [← mulVec_mulVec] at h1
    conv_lhs => rw [← h1]
    funext a
    simp only [mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hw]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv i)

end Gen

end CFSG.Quasithin.B45Ln
