module

public import CFSG.RankThree.PartOne.U5K.Kf.Witt
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem isHypTransport_mul_unitary {R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K}
    (hR : IsHypTransport h R) (P : primeFormUnitary h (idGram K 5)) :
    IsHypTransport (r := 2) (ε := 1) h
      (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R) := by
  have hP : (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ *
      ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
    have := mem_primeFormUnitary.1 P.2
    simpa [idGram] using this
  unfold IsHypTransport at hR ⊢
  have e : ((((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R).map h.bar)ᵀ *
      (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R) =
      (R.map h.bar)ᵀ * ((((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ *
        ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) * R := by
    rw [Matrix.map_mul, transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, hP, Matrix.mul_one]
  exact hR

theorem wmat_mulVec_single (ι : HypIndex 2 1 ≃ Fin 5) (u c : K) (x : HypIndex 2 1) :
    wmat ι u c *ᵥ Pi.single x 1 = wvec ι u c x := by
  funext t
  simp [wmat, Matrix.mulVec_single]

theorem diagonal_mulVec_ev (μ : Fin 5 → K) (s : Fin 5) :
    Matrix.diagonal μ *ᵥ ev s = μ s • ev s := by
  funext t
  by_cases hts : t = s
  · subst hts; simp [ev, Matrix.mulVec_diagonal]
  · simp [ev, Matrix.mulVec_diagonal, hts]

theorem diag_mulVec_wvec_inl (ι : HypIndex 2 1 ≃ Fin 5) (u c : K) (μ : Fin 5 → K) (a : Fin 2)
    (hμ : μ (ι (.inl a)) = μ (ι (.inr (.inr a)))) :
    Matrix.diagonal μ *ᵥ wvec ι u c (.inl a) = μ (ι (.inl a)) • wvec ι u c (.inl a) := by
  simp only [wvec, Matrix.mulVec_add, Matrix.mulVec_smul, diagonal_mulVec_ev, ← hμ]
  module

theorem diag_mulVec_wvec_inr_inr (ι : HypIndex 2 1 ≃ Fin 5) (u c : K) (μ : Fin 5 → K)
    (a : Fin 2) (hμ : μ (ι (.inl a)) = μ (ι (.inr (.inr a)))) :
    Matrix.diagonal μ *ᵥ wvec ι u c (.inr (.inr a)) =
      μ (ι (.inl a)) • wvec ι u c (.inr (.inr a)) := by
  simp only [wvec, Matrix.mulVec_add, Matrix.mulVec_smul, diagonal_mulVec_ev, ← hμ]
  module

theorem diag_mulVec_wvec_inr_inl (ι : HypIndex 2 1 ≃ Fin 5) (u c : K) (μ : Fin 5 → K)
    (k : Fin 1) :
    Matrix.diagonal μ *ᵥ wvec ι u c (.inr (.inl k)) =
      μ (ι (.inr (.inl k))) • wvec ι u c (.inr (.inl k)) := by
  simp only [wvec, diagonal_mulVec_ev]

theorem col_transport {R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K} (hR : IsHypTransport h R)
    {X : Matrix (Fin 5) (Fin 5) K} {x : HypIndex 2 1} {s : K}
    (hXs : X *ᵥ (R *ᵥ Pi.single x 1) = s • (R *ᵥ Pi.single x 1)) :
    (transportInv h R * X * R) *ᵥ Pi.single x 1 = s • Pi.single x 1 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXs, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]

theorem transportGLInv_gram {R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K}
    (hR : IsHypTransport h R) (X : primeFormUnitary h (idGram K 5)) :
    ((((transportGLInv hR (X : GL (Fin 5) K) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K)).map h.bar)ᵀ * hypGram 2 1 K *
      ((transportGLInv hR (X : GL (Fin 5) K) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) = hypGram 2 1 K := by
  refine (gramForm_isometry_iff h (hypGram 2 1 K) _).mp (fun u v => ?_)
  have hRA : R * ((transportGLInv hR (X : GL (Fin 5) K) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) =
        ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R := by
    rw [coe_transportGLInv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R, mul_transportInv hR, Matrix.one_mul]
  have hx' : ∀ u v : Fin 5 → K,
      gramForm h (1 : Matrix (Fin 5) (Fin 5) K)
        (((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ u)
        (((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
        gramForm h (1 : Matrix (Fin 5) (Fin 5) K) u v := by
    refine (gramForm_isometry_iff h 1 _).mpr ?_
    have := mem_primeFormUnitary.mp X.2
    simpa using this
  have h1 : gramForm h (hypGram 2 1 K) (((transportGLInv hR (X : GL (Fin 5) K) :
        GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ u)
      (((transportGLInv hR (X : GL (Fin 5) K) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ v) =
      stdHermForm h (2 * 2 + 1) (R *ᵥ (((transportGLInv hR (X : GL (Fin 5) K) :
        GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ u))
        (R *ᵥ (((transportGLInv hR (X : GL (Fin 5) K) : GL (HypIndex 2 1) K) :
          Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ v)) :=
    (stdHermForm_transport hR _ _).symm
  have h3 := stdHermForm_transport hR u v
  rw [stdHermForm_eq_gramForm] at h3
  rw [h1, mulVec_mulVec, mulVec_mulVec, hRA, ← mulVec_mulVec, ← mulVec_mulVec,
    stdHermForm_eq_gramForm, hx']
  exact h3

theorem transport_eq_diagonal {R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K}
    (hR : IsHypTransport h R) {X : Matrix (Fin 5) (Fin 5) K} (s : HypIndex 2 1 → K)
    (hs : ∀ x, X *ᵥ (R *ᵥ Pi.single x 1) = s x • (R *ᵥ Pi.single x 1)) :
    transportInv h R * X * R = Matrix.diagonal s := by
  ext r x
  have h1 := congrFun (col_transport h hR (hs x)) r
  have h2 : ((transportInv h R * X * R) *ᵥ Pi.single x 1) r = (transportInv h R * X * R) r x := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h2] at h1
  rw [h1]
  by_cases hrx : r = x
  · subst hrx; simp
  · simp [hrx]

theorem diagonal_eq_oddDiag (s : HypIndex 2 1 → K) (hfe : ∀ a, s (.inr (.inr a)) = s (.inl a))
    (hn : ∀ x, h.bar (s x) * s x = 1) :
    Matrix.diagonal s =
      oddDiag h (Matrix.diagonal fun a : Fin 2 => s (.inl a)) (s (.inr (.inl 0))) := by
  have hAA : ((Matrix.diagonal fun a : Fin 2 => s (.inl a)).map h.bar)ᵀ *
      Matrix.diagonal (fun a : Fin 2 => s (.inl a)) = 1 := by
    rw [Matrix.diagonal_map (by simp), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext a
    exact hn _
  have hinv : barInvT h (Matrix.diagonal fun a : Fin 2 => s (.inl a)) =
      Matrix.diagonal fun a : Fin 2 => s (.inl a) := by
    unfold barInvT
    rw [Matrix.transpose_nonsing_inv]
    exact Matrix.inv_eq_right_inv hAA
  ext r c
  rcases r with i | k | i <;> rcases c with j | l | j
  all_goals simp [oddDiag, hinv, Matrix.diagonal_apply, hfe]
  all_goals first | done | (fin_cases k; fin_cases l; simp)

end CFSG.RankThree.PartOne.U5K.Kf
