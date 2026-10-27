module

public import CFSG.LocalAnalysis.ZStar.PadicTrace
public import Mathlib.RingTheory.SimpleRing.Principal
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace ZStar.WedderburnBlock

noncomputable section

universe u v

variable {K : Type u} {G : Type v}

abbrev BlockProduct (K : Type u) {n : ℕ} (d : Fin n → ℕ) :=
  (i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) K

@[expose] noncomputable def selectedComponents [Field K] {n : ℕ} {d : Fin n → ℕ}
    (E : BlockProduct K d) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => E i = 1

@[expose] noncomputable def selectedIndices [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    (φ : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (e : MonoidAlgebra K G) : Finset (Fin n) :=
  selectedComponents (φ e)

@[simp]
theorem mem_selectedComponents [Field K] {n : ℕ} {d : Fin n → ℕ}
    {E : BlockProduct K d} {i : Fin n} :
    i ∈ selectedComponents E ↔ E i = 1 := by
  simp [selectedComponents]

@[simp]
theorem mem_selectedIndices [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    {φ : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d}
    {e : MonoidAlgebra K G} {i : Fin n} :
    i ∈ selectedIndices φ e ↔ φ e i = 1 := by
  simp [selectedIndices]

theorem component_eq_zero_or_one [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    (φ : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    {e : MonoidAlgebra K G}
    (hecentral : e ∈ Submonoid.center (MonoidAlgebra K G))
    (heidem : e * e = e) (i : Fin n) :
    φ e i = 0 ∨ φ e i = 1 := by
  have hcomm (p q : Fin (d i)) :
      Commute (Matrix.single p q (1 : K)) (φ e i) := by
    let y : BlockProduct K d := Pi.single i (Matrix.single p q (1 : K))
    let x : MonoidAlgebra K G := φ.symm y
    have hc := (Submonoid.mem_center_iff.mp hecentral) x
    have hc' := congrArg (fun z : BlockProduct K d => z i)
      (congrArg φ hc)
    rw [commute_iff_eq]
    simpa [x, y] using hc'
  have hrange : φ e i ∈ Set.range (Matrix.scalar (Fin (d i))) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro p q hpq
    exact hcomm p q
  obtain ⟨c, hc⟩ := hrange
  have hidem_i : φ e i * φ e i = φ e i := by
    have h := congrArg (fun z : BlockProduct K d => z i)
      (congrArg φ heidem)
    simpa using h
  by_cases hd : d i = 0
  · left
    ext p q
    have hp := p.isLt
    simp [hd] at hp
  · let p : Fin (d i) := ⟨0, Nat.pos_of_ne_zero hd⟩
    let _ : Nonempty (Fin (d i)) := ⟨p⟩
    have hcidem : c * c = c := by
      have hmatrix :
          Matrix.scalar (Fin (d i)) c * Matrix.scalar (Fin (d i)) c =
            Matrix.scalar (Fin (d i)) c := by
        rw [hc]
        exact hidem_i
      have hentry := congrArg
        (fun M : Matrix (Fin (d i)) (Fin (d i)) K => M p p) hmatrix
      simpa [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal] using hentry
    have hfactor : c * (c - 1) = 0 := by
      rw [mul_sub, mul_one, hcidem, sub_self]
    rcases mul_eq_zero.mp hfactor with hc0 | hc1
    · left
      rw [← hc, hc0, map_zero]
    · right
      have hc_one : c = 1 := sub_eq_zero.mp hc1
      rw [← hc, hc_one, map_one]

private theorem stdBasis_repr_apply [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (i j : ι) :
    ((Matrix.stdBasis K ι ι).repr M) (i, j) = M i j := by
  simp [Matrix.stdBasis]

theorem trace_matrix_mulLeftRight [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι K) :
    LinearMap.trace K (Matrix ι ι K)
        (LinearMap.mulLeftRight K (A, B)) =
      Matrix.trace A * Matrix.trace B := by
  let b := Matrix.stdBasis K ι ι
  rw [LinearMap.trace_eq_matrix_trace K b]
  change
    (∑ ij : ι × ι,
      ((LinearMap.toMatrix b b)
        (LinearMap.mulLeftRight K (A, B))) ij ij) =
      (∑ i : ι, A i i) * ∑ j : ι, B j j
  calc
    (∑ ij : ι × ι,
      ((LinearMap.toMatrix b b)
        (LinearMap.mulLeftRight K (A, B))) ij ij) =
        ∑ ij : ι × ι, A ij.1 ij.1 * B ij.2 ij.2 := by
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ hij
      rw [LinearMap.toMatrix_apply]
      change (b.repr
        ((LinearMap.mulLeftRight K (A, B)) (b (i, j)))) (i, j) = _
      rw [show b (i, j) = Matrix.single i j (1 : K) by
        exact Matrix.stdBasis_eq_single K i j]
      rw [stdBasis_repr_apply, LinearMap.mulLeftRight_apply]
      calc
        (A * Matrix.single i j (1 : K) * B) i j =
            ∑ k : ι, (A * Matrix.single i j (1 : K)) i k * B k j :=
          Matrix.mul_apply
        _ = (A * Matrix.single i j (1 : K)) i j * B j j := by
          rw [Finset.sum_eq_single j]
          · intro k hk hkj
            rw [Matrix.mul_single_apply_of_ne (1 : K) i j i k hkj]
            simp
          · simp
        _ = A i i * B j j := by
          rw [Matrix.mul_single_apply_same]
          simp
    _ = (∑ i : ι, A i i) * ∑ j : ι, B j j := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ i : ι, ∑ j : ι, A i i * B j j) =
            ∑ i : ι, A i i * ∑ j : ι, B j j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = (∑ i : ι, A i i) * ∑ j : ι, B j j := by
          rw [Finset.sum_mul]

private noncomputable def blockProductBasis [Field K]
    {n : ℕ} (d : Fin n → ℕ) :
    Module.Basis ((i : Fin n) × (Fin (d i) × Fin (d i))) K
      (BlockProduct K d) :=
  Pi.basis fun i => Matrix.stdBasis K (Fin (d i)) (Fin (d i))

private theorem blockProductBasis_repr_apply [Field K]
    {n : ℕ} {d : Fin n → ℕ}
    (X : BlockProduct K d)
    (s : (i : Fin n) × (Fin (d i) × Fin (d i))) :
    ((blockProductBasis d).repr X) s = X s.1 s.2.1 s.2.2 := by
  unfold blockProductBasis
  rw [Pi.basis_repr]
  exact stdBasis_repr_apply _ _ _

private theorem trace_blockProduct_mulLeftRight [Field K]
    {n : ℕ} {d : Fin n → ℕ}
    (A B : BlockProduct K d) :
    LinearMap.trace K (BlockProduct K d)
        (LinearMap.mulLeftRight K (A, B)) =
      ∑ i : Fin n, Matrix.trace (A i) * Matrix.trace (B i) := by
  let b := blockProductBasis (K := K) d
  rw [LinearMap.trace_eq_matrix_trace K b]
  change
    (∑ s : (i : Fin n) × (Fin (d i) × Fin (d i)),
      ((LinearMap.toMatrix b b)
        (LinearMap.mulLeftRight K (A, B))) s s) = _
  calc
    (∑ s : (i : Fin n) × (Fin (d i) × Fin (d i)),
      ((LinearMap.toMatrix b b)
        (LinearMap.mulLeftRight K (A, B))) s s) =
        ∑ s : (i : Fin n) × (Fin (d i) × Fin (d i)),
          A s.1 s.2.1 s.2.1 * B s.1 s.2.2 s.2.2 := by
      apply Finset.sum_congr rfl
      rintro ⟨i, ⟨p, q⟩⟩ hs
      rw [LinearMap.toMatrix_apply]
      change (b.repr
        ((LinearMap.mulLeftRight K (A, B)) (b ⟨i, (p, q)⟩)))
          ⟨i, (p, q)⟩ = _
      rw [show b ⟨i, (p, q)⟩ =
          Pi.single i (Matrix.single p q (1 : K)) by
        dsimp [b, blockProductBasis]
        rw [Pi.basis_apply, Matrix.stdBasis_eq_single]]
      rw [blockProductBasis_repr_apply, LinearMap.mulLeftRight_apply]
      simp only [Pi.mul_apply, Pi.single_eq_same]
      calc
        (A i * Matrix.single p q (1 : K) * B i) p q =
            ∑ k : Fin (d i),
              (A i * Matrix.single p q (1 : K)) p k * B i k q :=
          Matrix.mul_apply
        _ = (A i * Matrix.single p q (1 : K)) p q * B i q q := by
          rw [Finset.sum_eq_single q]
          · intro k hk hkq
            rw [Matrix.mul_single_apply_of_ne (1 : K) p q p k hkq]
            simp
          · simp
        _ = A i p p * B i q q := by
          rw [Matrix.mul_single_apply_same]
          simp
    _ = ∑ i : Fin n, Matrix.trace (A i) * Matrix.trace (B i) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.sum_prod_type]
      change (∑ p : Fin (d i), ∑ q : Fin (d i),
        A i p p * B i q q) =
        (∑ p : Fin (d i), A i p p) * ∑ q : Fin (d i), B i q q
      calc
        (∑ p : Fin (d i), ∑ q : Fin (d i), A i p p * B i q q) =
            ∑ p : Fin (d i), A i p p * ∑ q : Fin (d i), B i q q := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
        _ = (∑ p : Fin (d i), A i p p) * ∑ q : Fin (d i), B i q q := by
          rw [Finset.sum_mul]

private theorem trace_blockProduct_mulLeftRight_of_zero_or_one [Field K]
    {n : ℕ} {d : Fin n → ℕ}
    (A B E : BlockProduct K d)
    (hE : ∀ i, E i = 0 ∨ E i = 1) :
    LinearMap.trace K (BlockProduct K d)
        (LinearMap.mulLeftRight K (A, B * E)) =
      ∑ i ∈ selectedComponents E,
        Matrix.trace (A i) * Matrix.trace (B i) := by
  classical
  rw [trace_blockProduct_mulLeftRight]
  calc
    (∑ i : Fin n,
      Matrix.trace (A i) * Matrix.trace ((B * E) i)) =
        ∑ i : Fin n, if E i = 1 then
          Matrix.trace (A i) * Matrix.trace (B i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hone : E i = 1
      · simp [hone]
      · have hzero : E i = 0 := (hE i).resolve_right hone
        rw [ite_eq_right hone]
        simp [hzero]
    _ = ∑ i ∈ selectedComponents E,
        Matrix.trace (A i) * Matrix.trace (B i) := by
      rw [selectedComponents, Finset.sum_filter]

theorem trace_mulLeftRight_mul_centralIdempotent
    [Field K] [Group G] [Fintype G]
    {n : ℕ} {d : Fin n → ℕ}
    (φ : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (e : MonoidAlgebra K G)
    (hecentral : e ∈ Submonoid.center (MonoidAlgebra K G))
    (heidem : e * e = e)
    (a b : MonoidAlgebra K G) :
    LinearMap.trace K (MonoidAlgebra K G)
        (LinearMap.mulLeftRight K (a, b * e)) =
      ∑ i ∈ selectedIndices φ e,
        Matrix.trace (φ a i) * Matrix.trace (φ b i) := by
  have hconj :
      φ.toLinearEquiv.conj (LinearMap.mulLeftRight K (a, b * e)) =
        LinearMap.mulLeftRight K (φ a, φ b * φ e) := by
    simpa only [Prod.map_apply', map_mul] using
      AlgEquiv.linearEquivConj_mulLeftRight φ (a, b * e)
  calc
    LinearMap.trace K (MonoidAlgebra K G)
        (LinearMap.mulLeftRight K (a, b * e)) =
        LinearMap.trace K (BlockProduct K d)
          (φ.toLinearEquiv.conj (LinearMap.mulLeftRight K (a, b * e))) :=
      (LinearMap.trace_conj'
        (LinearMap.mulLeftRight K (a, b * e)) φ.toLinearEquiv).symm
    _ = LinearMap.trace K (BlockProduct K d)
        (LinearMap.mulLeftRight K (φ a, φ b * φ e)) := by rw [hconj]
    _ = ∑ i ∈ selectedIndices φ e,
        Matrix.trace (φ a i) * Matrix.trace (φ b i) := by
      exact trace_blockProduct_mulLeftRight_of_zero_or_one
        (φ a) (φ b) (φ e) (component_eq_zero_or_one φ hecentral heidem)

end

end ZStar.WedderburnBlock

end CFSG
