module

public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.RankThree.Literature.Beisiegel

open MvPolynomial

theorem totalDegree_zsmul_le {σ R : Type*} [CommRing R] (n : ℤ) (f : MvPolynomial σ R) :
    (n • f).totalDegree ≤ f.totalDegree := by
  rw [zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  calc (C (n : R) * f).totalDegree ≤ (C (n : R)).totalDegree + f.totalDegree :=
        totalDegree_mul _ _
    _ = f.totalDegree := by rw [totalDegree_C, zero_add]

theorem totalDegree_det_le {σ R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin k) (Fin k) (MvPolynomial σ R)) (hM : ∀ j l, (M j l).totalDegree ≤ 1) :
    M.det.totalDegree ≤ k := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le fun τ _ => ?_
  rw [Units.smul_def]
  refine (totalDegree_zsmul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (τ i) i).totalDegree ≤ ∑ _i : Fin k, 1 := Finset.sum_le_sum fun i _ => hM _ _
    _ = k := by simp

theorem isAlt_toBilin' {K : Type*} [Field K] {k : ℕ} (N : Matrix (Fin k) (Fin k) K)
    (hdiag : ∀ j, N j j = 0) (hskew : ∀ j l, N l j = -N j l) :
    (Matrix.toBilin' N).IsAlt := by
  intro v
  let U : Matrix (Fin k) (Fin k) K := Matrix.of fun j l => if j < l then N j l else 0
  have hN : N = U - U.transpose := by
    ext j l
    simp only [U, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy j l with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · have h1 : N j l = -N l j := hskew l j
      simp [h, not_lt.mpr h.le, h1]
  rw [Matrix.toBilin'_apply', hN, Matrix.sub_mulVec, dotProduct_sub, Matrix.mulVec_transpose,
    dotProduct_comm v (Matrix.vecMul v U), ← Matrix.dotProduct_mulVec, sub_self]

variable {p : ℕ} [Fact p.Prime]

theorem exists_sq_eq_det_mul {m k : ℕ}
    (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) (ZMod p)))
    (hdiag : ∀ j, M j j = 0) (hskew : ∀ j l, M l j = -M j l) :
    ∃ c u : MvPolynomial (Fin m) (ZMod p), c * c = M.det * u ∧ u * u = 1 := by
  classical
  let R := MvPolynomial (Fin m) (ZMod p)
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  let N : Matrix (Fin k) (Fin k) K := M.map φ
  let B : LinearMap.BilinForm K (Fin k → K) := Matrix.toBilin' N
  have hBalt : B.IsAlt := isAlt_toBilin' N (fun j => by simp [N, hdiag])
    (fun j l => by simp only [N, Matrix.map_apply]; rw [hskew j l, map_neg])
  have hdetN : φ M.det = N.det := RingHom.map_det φ M
  have hBN : LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin k)) B = N := by
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
  by_cases hnd : B.Nondegenerate
  · obtain ⟨r, b, hb⟩ := hBalt.exists_basis_toMatrix_eq_J hnd
    have hcard : Fintype.card (Fin r ⊕ Fin r) = Fintype.card (Fin k) := by
      rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun, Fintype.card_fin]
    let e : Fin r ⊕ Fin r ≃ Fin k := Fintype.equivOfCardEq hcard
    let b' := b.reindex e
    have hb' : LinearMap.BilinForm.toMatrix b' B = Matrix.reindex e e (Matrix.J (Fin r) K) := by
      rw [← hb]
      ext x y
      simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        b', Module.Basis.reindex_apply]
    have key := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b' (Pi.basisFun K (Fin k)) B
    rw [hb', hBN] at key
    set Pm := b'.toMatrix ⇑(Pi.basisFun K (Fin k))
    have hdet : N.det = Pm.det * Pm.det * (Matrix.J (Fin r) K).det := by
      rw [← key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_reindex_self]
      ring
    have hJ : (Matrix.J (Fin r) R).map φ = Matrix.J (Fin r) K := by
      ext x y
      rcases x with x | x <;> rcases y with y | y <;>
        simp [Matrix.J, Matrix.one_apply, apply_ite φ]
    let u : R := (Matrix.J (Fin r) R).det
    have hu : φ u = (Matrix.J (Fin r) K).det := by
      rw [RingHom.map_det]
      exact congrArg Matrix.det hJ
    have huu : u * u = 1 := Matrix.J_det_mul_J_det (Fin r) R
    have huuK : (Matrix.J (Fin r) K).det * (Matrix.J (Fin r) K).det = 1 :=
      Matrix.J_det_mul_J_det (Fin r) K
    have hsq : φ (M.det * u) = Pm.det ^ 2 := by
      rw [map_mul, hdetN, hu, hdet]
      calc Pm.det * Pm.det * (Matrix.J (Fin r) K).det * (Matrix.J (Fin r) K).det
          = Pm.det * Pm.det * ((Matrix.J (Fin r) K).det * (Matrix.J (Fin r) K).det) := by ring
        _ = Pm.det ^ 2 := by rw [huuK, mul_one, sq]
    have hint : IsIntegral R (Pm.det ^ 2) := by
      rw [← hsq]
      exact isIntegral_algebraMap
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
      (K := K) two_pos hint
    refine ⟨c, u, IsFractionRing.injective R K ?_, huu⟩
    change φ (c * c) = φ (M.det * u)
    rw [hsq, map_mul]
    change algebraMap R K c * algebraMap R K c = _
    rw [hc, sq]
  · have hD : N.det = 0 := by
      by_contra hne
      exact hnd ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
        (Pi.basisFun K (Fin k))).mpr (by rwa [hBN]))
    have hD' : M.det = 0 := IsFractionRing.injective R K (by
      change φ M.det = φ 0
      rw [hdetN, hD, map_zero])
    exact ⟨0, 1, by simp [hD'], mul_one 1⟩

theorem two_mul_le_of_det_ne_zero {k m : ℕ} (hk : 0 < k)
    (A : Fin m → Matrix (Fin k) (Fin k) (ZMod p)) (hdiag : ∀ i j, A i j j = 0)
    (hskew : ∀ i j l, A i l j = -A i j l)
    (hdet : ∀ a : Fin m → ZMod p, a ≠ 0 → (∑ i, a i • A i).det ≠ 0) : 2 * m ≤ k := by
  classical
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) (ZMod p)) :=
    Matrix.of fun j l => ∑ i, X i * C (A i j l)
  have heval : ∀ a : Fin m → ZMod p, eval a M.det = (∑ i, a i • A i).det := by
    intro a
    rw [RingHom.map_det]
    congr 1
    ext j l
    simp [M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hdeg : M.det.totalDegree ≤ k := by
    refine totalDegree_det_le M fun j l => ?_
    simp only [M, Matrix.of_apply]
    refine totalDegree_finsetSum_le fun i _ => ?_
    calc (X i * C (A i j l)).totalDegree ≤ (X i).totalDegree + (C (A i j l)).totalDegree :=
          totalDegree_mul _ _
      _ ≤ 1 := by rw [totalDegree_X, totalDegree_C]
  obtain ⟨c, u, hcu, huu⟩ := exists_sq_eq_det_mul M (fun j => by simp [M, hdiag])
    (fun j l => by
      simp only [M, Matrix.of_apply]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hskew i j l, map_neg, mul_neg])
  have hD : M.det = c * c * u := by
    rw [hcu, mul_assoc, huu, mul_one]
  have hcdeg : 2 * c.totalDegree ≤ k := by
    by_cases hc : c = 0
    · rw [hc, totalDegree_zero, mul_zero]
      exact Nat.zero_le _
    · have hu0 : u ≠ 0 := fun h => by
        rw [h, zero_mul] at huu
        exact zero_ne_one huu
      have hcc : c * c ≠ 0 := mul_ne_zero hc hc
      have h1 := totalDegree_mul_of_isDomain hcc hu0
      have h2 := totalDegree_mul_of_isDomain hc hc
      rw [← hD] at h1
      omega
  by_contra hlt
  push Not at hlt
  have hlt' : c.totalDegree < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions (K := ZMod p) p hlt'
  have h0 : eval 0 c = 0 := by
    have : eval 0 c * eval 0 c = 0 := by
      have h := congrArg (eval (0 : Fin m → ZMod p)) hcu
      rw [map_mul, map_mul, heval] at h
      have : (∑ i, (0 : Fin m → ZMod p) i • A i) = 0 := by simp
      have hne : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      rw [this, Matrix.det_zero, zero_mul] at h
      exact h
    exact mul_self_eq_zero.mp this
  have hpos : 0 < Fintype.card { x : Fin m → ZMod p // eval x c = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : 1 < Fintype.card { x : Fin m → ZMod p // eval x c = 0 } := by
    have := Nat.le_of_dvd hpos hdvd
    have hp2 := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨⟨a, ha⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hone ⟨0, h0⟩
  have ha0 : a ≠ 0 := fun h => hne (Subtype.ext h)
  apply hdet a ha0
  rw [← heval, hD, map_mul, map_mul, ha, zero_mul, zero_mul]

end CFSG.RankThree.Literature.Beisiegel
