module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.Sporadic.Co1Schreier.Descent

open Matrix

theorem exists_ne_zero_of_map {F K : Type*} [Field F] [Field K] [Algebra F K] {ι κ : Type*}
    [Fintype ι] [Finite κ] (N : κ → ι → F) {v : ι → K} (hv : v ≠ 0)
    (h : ∀ k, ∑ i, v i * algebraMap F K (N k i) = 0) :
    ∃ u : ι → F, u ≠ 0 ∧ ∀ k, ∑ i, u i * N k i = 0 := by
  by_contra hne
  have hli : LinearIndependent F fun i k => N k i := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hgi
    refine hne ⟨g, fun h0 => hgi (congrFun h0 i), fun k => ?_⟩
    have hk := congrFun hg k
    rw [Finset.sum_apply, Pi.zero_apply] at hk
    simpa only [Pi.smul_apply, smul_eq_mul] using hk
  have hli' := (linearIndependent_algebraMap_comp_iff (S := K)).mpr hli
  rw [Fintype.linearIndependent_iff] at hli'
  refine hv (funext fun i => hli' v (funext fun k => ?_) i)
  rw [Finset.sum_apply, Pi.zero_apply]
  simpa only [Pi.smul_apply, Function.comp_apply, smul_eq_mul] using h k

@[expose] def coeff {R : Type*} [Ring R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (k l p q : Fin n) : R :=
  (if k = p then P q l else 0) - if q = l then Q k p else 0

theorem intertwine_sum {R : Type*} [CommRing R] {n : ℕ} (T P Q : Matrix (Fin n) (Fin n) R)
    (k l : Fin n) :
    ∑ pq : Fin n × Fin n, T pq.1 pq.2 * coeff P Q k l pq.1 pq.2 = (T * P - Q * T) k l := by
  simp only [coeff, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.mul_apply]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  congr 1
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem map_coeff {F K : Type*} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) F) (k l p q : Fin n) :
    algebraMap F K (coeff P Q k l p q) =
      coeff (P.map (algebraMap F K)) (Q.map (algebraMap F K)) k l p q := by
  unfold coeff
  rw [map_sub, apply_ite (algebraMap F K), apply_ite (algebraMap F K), map_zero,
    Matrix.map_apply, Matrix.map_apply]

theorem exists_intertwiner_of_map {F K : Type*} [Field F] [Field K] [Algebra F K] {G : Type*}
    [Finite G] {n : ℕ} (P Q : G → Matrix (Fin n) (Fin n) F) {S : Matrix (Fin n) (Fin n) K}
    (hS : S ≠ 0) (h : ∀ x, S * (P x).map (algebraMap F K) = (Q x).map (algebraMap F K) * S) :
    ∃ T : Matrix (Fin n) (Fin n) F, T ≠ 0 ∧ ∀ x, T * P x = Q x * T := by
  have hv : (fun pq : Fin n × Fin n => S pq.1 pq.2) ≠ 0 := fun h0 =>
    hS (Matrix.ext fun i j => congrFun h0 (i, j))
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_map
    (fun (xkl : G × Fin n × Fin n) (pq : Fin n × Fin n) =>
      coeff (P xkl.1) (Q xkl.1) xkl.2.1 xkl.2.2 pq.1 pq.2) hv (fun xkl => by
    simp only [map_coeff]
    rw [intertwine_sum, h xkl.1, sub_self, Matrix.zero_apply])
  refine ⟨Matrix.of fun p q => u (p, q), fun h0 => hu (funext fun pq => ?_), fun x => ?_⟩
  · have := congrFun (congrFun h0 pq.1) pq.2
    rwa [Matrix.of_apply] at this
  · rw [← sub_eq_zero]
    ext k l
    rw [← intertwine_sum, Matrix.zero_apply]
    exact hu0 (x, k, l)

theorem isUnit_of_intertwiner {F K : Type*} [Field F] [Field K] [Algebra F K] {G : Type*}
    {n : ℕ} (P Q : G → Matrix (Fin n) (Fin n) F)
    (hirr : ∀ S : Submodule K (Fin n → K),
      (∀ x, ∀ v ∈ S, (P x).map (algebraMap F K) *ᵥ v ∈ S) → S = ⊥ ∨ S = ⊤)
    {T : Matrix (Fin n) (Fin n) F} (hT : T ≠ 0) (hTP : ∀ x, T * P x = Q x * T) : IsUnit T := by
  have hker := hirr (LinearMap.ker (T.map (algebraMap F K)).mulVecLin) (fun x v hv => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hTP x, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      hv, Matrix.mulVec_zero])
  rcases hker with h | h
  · have hinj : Function.Injective (T.map (algebraMap F K)).mulVec := by
      have := LinearMap.ker_eq_bot.mp h
      rwa [Matrix.coe_mulVecLin] at this
    have hu := Matrix.mulVec_injective_iff_isUnit.mp hinj
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu ⊢
    intro h0
    apply hu
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · exfalso
    apply hT
    ext i j
    have hm : Pi.single j 1 ∈ LinearMap.ker (T.map (algebraMap F K)).mulVecLin := by
      rw [h]
      trivial
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_single_one] at hm
    have hij := congrFun hm i
    rw [Matrix.col_apply, Matrix.map_apply, Pi.zero_apply] at hij
    exact (algebraMap F K).injective (hij.trans (map_zero _).symm)

end CFSG.Sporadic.Co1Schreier.Descent
