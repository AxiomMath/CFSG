module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.Matrix.Mul
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.OmegaIsoCols

open Matrix QuadraticMap CFSG.PGLModel

theorem map_mulVec_of_cols {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (Q : QuadraticMap R (ι → R) R) (M : Matrix ι ι R)
    (h1 : ∀ i, Q (M.col i) = Q (Pi.single i 1))
    (h2 : ∀ i j, i ≠ j → Q (M.col i + M.col j) = Q (Pi.single i 1 + Pi.single j 1))
    (v : ι → R) : Q (M *ᵥ v) = Q v := by
  have hp : ∀ i j, i ≠ j → polar Q (M.col i) (M.col j) = polar Q (Pi.single i 1) (Pi.single j 1) :=
    fun i j h => by rw [polar, polar, h2 i j h, h1, h1]
  have hM : M *ᵥ v = ∑ i, v i • M.col i := by
    ext r
    simp [mulVec, dotProduct, mul_comm]
  have hv : v = ∑ i, v i • (Pi.single i (1 : R) : ι → R) := by
    ext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    simp
  conv_rhs => rw [hv]
  rw [hM, Q.map_sum, Q.map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Q.map_smul, Q.map_smul, h1]
  · refine Finset.sum_congr rfl fun p hp' => ?_
    induction p using Sym2.ind with
    | _ i j =>
      have hij : i ≠ j := fun h => (Finset.mem_filter.1 hp').2 (by simp [h])
      simp only [Sym2.map_mk, polarSym2_sym2Mk, polar_smul_left, polar_smul_right, hp i j hij]

@[expose] noncomputable def plusQ (m : ℕ) (K : Type*) [Field K] : QuadraticMap K (Fin m ⊕ Fin m → K) K :=
  ∑ i : Fin m, QuadraticMap.proj (R := K) (Sum.inl i) (Sum.inr i)

theorem plusQ_apply (m : ℕ) {K : Type*} [Field K] (v : Fin m ⊕ Fin m → K) :
    plusQ m K v = plusQuadForm m v := by
  simp [plusQ, plusQuadForm, QuadraticMap.proj_apply]

@[expose] noncomputable def minusQ (m : ℕ) {K : Type*} [Field K] (b c : K) :
    QuadraticMap K (Fin m ⊕ Fin m ⊕ Fin 2 → K) K :=
  ∑ i : Fin m, QuadraticMap.proj (R := K) (Sum.inl i) (Sum.inr (Sum.inl i)) +
    QuadraticMap.proj (R := K) (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) +
    b • QuadraticMap.proj (R := K) (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) +
    c • QuadraticMap.proj (R := K) (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1))

theorem minusQ_apply (m : ℕ) {K : Type*} [Field K] (b c : K) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    minusQ m b c v = minusQuadForm m b c v := by
  simp [minusQ, minusQuadForm, QuadraticMap.proj_apply, _root_.sq, mul_assoc]

theorem plus_of_cols {m : ℕ} {K : Type*} [Field K] (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (h1 : ∀ i, plusQuadForm m (M.col i) = plusQuadForm m (Pi.single i 1))
    (h2 : ∀ i j, i ≠ j →
      plusQuadForm m (M.col i + M.col j) = plusQuadForm m (Pi.single i 1 + Pi.single j 1))
    (v : Fin m ⊕ Fin m → K) : plusQuadForm m (M *ᵥ v) = plusQuadForm m v := by
  simp only [← plusQ_apply] at h1 h2 ⊢
  exact map_mulVec_of_cols _ M h1 h2 v

theorem minus_of_cols {m : ℕ} {K : Type*} [Field K] {b c : K}
    (M : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (h1 : ∀ i, minusQuadForm m b c (M.col i) = minusQuadForm m b c (Pi.single i 1))
    (h2 : ∀ i j, i ≠ j → minusQuadForm m b c (M.col i + M.col j) =
      minusQuadForm m b c (Pi.single i 1 + Pi.single j 1))
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) : minusQuadForm m b c (M *ᵥ v) = minusQuadForm m b c v := by
  simp only [← minusQ_apply] at h1 h2 ⊢
  exact map_mulVec_of_cols _ M h1 h2 v

end CFSG.RankThree.PartTwo.Sec4.Census.OmegaIsoCols
