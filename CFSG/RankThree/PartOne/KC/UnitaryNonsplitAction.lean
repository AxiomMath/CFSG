module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeFixed
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitCount

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary

section Act

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {x : gramSU h (idGram K n)} (L : LiftData h n p x)

include L in
theorem LiftData.actEnd_aeval {α : MulAut (primeFormP h (idGram K n))}
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x))
    {M : primeFormUnitary h (idGram K n)} {σ : K ≃+* K}
    (hMσ : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, σ⟩ = α) (g : K[X]) :
    actEndHom (h := h) L.three_le L.four_le α (aeval (idEnd x) g) =
      aeval (idEnd x) (g.map (σ : K →+* K)) := by
  have hφ : ∀ c : K, (actEndHom (h := h) L.three_le L.four_le α :
        Module.End K (Fin n → K) →+* Module.End K (Fin n → K))
        (algebraMap K (Module.End K (Fin n → K)) c) =
      algebraMap K (Module.End K (Fin n → K)) ((σ : K →+* K) c) := by
    intro c
    have h1 : algebraMap K (Module.End K (Fin n → K)) c =
        toEnd (algebraMap K (Matrix (Fin n) (Fin n) K) c) := (toEnd.commutes c).symm
    have h2 : algebraMap K (Module.End K (Fin n → K)) (σ c) =
        toEnd (algebraMap K (Matrix (Fin n) (Fin n) K) (σ c)) := (toEnd.commutes (σ c)).symm
    change actEndHom (h := h) L.three_le L.four_le α (algebraMap K (Module.End K (Fin n → K)) c) =
      algebraMap K (Module.End K (Fin n → K)) (σ c)
    rw [h1, h2, actEndHom_toEnd, ← hMσ, idAct_primeFormPsi, idMatAction_mk]
    congr 1
    have h3 : (algebraMap K (Matrix (Fin n) (Fin n) K) c).map σ =
        algebraMap K (Matrix (Fin n) (Fin n) K) (σ c) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [h3, ← Algebra.commutes (σ c) _, mul_assoc, Units.mul_inv, mul_one]
  have h1 := ringHom_aeval_semilinear (actEndHom (h := h) L.three_le L.four_le α :
        Module.End K (Fin n → K) →+* Module.End K (Fin n → K)) (σ : K →+* K) hφ (idEnd x) g
  have h2 := L.actEnd_fix α hα
  change actEndHom (h := h) L.three_le L.four_le α (aeval (idEnd x) g) =
    aeval (actEndHom (h := h) L.three_le L.four_le α (idEnd x)) (g.map (σ : K →+* K)) at h1
  rw [h2] at h1
  exact h1

include L in
theorem LiftData.map_minpoly {α : MulAut (primeFormP h (idGram K n))}
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x))
    {M : primeFormUnitary h (idGram K n)} {σ : K ≃+* K}
    (hMσ : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, σ⟩ = α) :
    (minpoly K (idEnd x)).map (σ : K →+* K) = minpoly K (idEnd x) := by
  have h1 := L.actEnd_aeval hα hMσ (minpoly K (idEnd x))
  rw [minpoly.aeval, map_zero] at h1
  have hμ := minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) (idEnd x))
  exact eq_of_monic_of_dvd_of_natDegree_le hμ (hμ.map _) (minpoly.dvd K (idEnd x) h1.symm)
    (by rw [natDegree_map])

include L in
theorem LiftData.map_mem_primaryFactors {α : MulAut (primeFormP h (idGram K n))}
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x))
    {M : primeFormUnitary h (idGram K n)} {σ : K ≃+* K}
    (hMσ : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, σ⟩ = α)
    {a : K[X]} (ha : a ∈ primaryFactors (idEnd x)) :
    a.map (σ : K →+* K) ∈ primaryFactors (idEnd x) := by
  rw [mem_primaryFactors] at ha ⊢
  refine ⟨?_, ha.2.1.map _, ?_⟩
  · have := (MulEquiv.irreducible_iff (Polynomial.mapEquiv σ)).mpr ha.1
    rwa [Polynomial.mapEquiv_apply] at this
  · have := Polynomial.map_dvd (σ : K →+* K) ha.2.2
    rwa [L.map_minpoly hα hMσ] at this

include L in
theorem LiftData.aeval_map_primaryIdempotent (σ : K ≃+* K)
    (hσF : ∀ a ∈ primaryFactors (idEnd x), a.map (σ : K →+* K) = a)
    {i : K[X]} (hi : i ∈ primaryFactors (idEnd x)) :
    aeval (idEnd x) ((primaryIdempotent (idEnd x) i).map (σ : K →+* K)) =
      primaryProjection (idEnd x) i := by
  classical
  have hsq := L.squarefree_idEnd
  set g := primaryIdempotent (idEnd x) i with hg
  obtain ⟨⟨q, hq⟩, hgb, -⟩ := primaryIdempotent_spec hsq hi
  have hdvd : minpoly K (idEnd x) ∣ g.map (σ : K →+* K) - g := by
    rw [← prod_primaryFactors hsq]
    refine Finset.prod_dvd_of_coprime pairwise_isCoprime_primaryFactors fun b hb => ?_
    by_cases hbi : b = i
    · subst hbi
      have h1 : b ∣ g.map (σ : K →+* K) - 1 := by
        have := Polynomial.map_dvd (σ : K →+* K) (show b ∣ g - 1 from ⟨q, hq⟩)
        rwa [hσF b hb, Polynomial.map_sub, Polynomial.map_one] at this
      have h2 : b ∣ g - 1 := ⟨q, hq⟩
      have := dvd_sub h1 h2
      rwa [show g.map (σ : K →+* K) - 1 - (g - 1) = g.map (σ : K →+* K) - g by ring] at this
    · have h1 : b ∣ g := hgb b hb hbi
      have h2 : b ∣ g.map (σ : K →+* K) := by
        have := Polynomial.map_dvd (σ : K →+* K) h1
        rwa [hσF b hb] at this
      exact dvd_sub h2 h1
  obtain ⟨r, hr⟩ := hdvd
  have h3 : aeval (idEnd x) (g.map (σ : K →+* K)) - aeval (idEnd x) g = 0 := by
    rw [← map_sub, hr, map_mul, minpoly.aeval, zero_mul]
  rw [sub_eq_zero] at h3
  exact h3

include L in
theorem LiftData.actEnd_primaryProjection {α : MulAut (primeFormP h (idGram K n))}
    (hα : α * primeFormConjHom h (idGram K n) (liftUnitary x) * α⁻¹ =
      primeFormConjHom h (idGram K n) (liftUnitary x))
    {M : primeFormUnitary h (idGram K n)} {σ : K ≃+* K}
    (hMσ : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, σ⟩ = α)
    (hσF : ∀ a ∈ primaryFactors (idEnd x), a.map (σ : K →+* K) = a)
    {i : K[X]} (hi : i ∈ primaryFactors (idEnd x)) :
    actEndHom (h := h) L.three_le L.four_le α (primaryProjection (idEnd x) i) =
      primaryProjection (idEnd x) i := by
  have h1 := L.actEnd_aeval hα hMσ (primaryIdempotent (idEnd x) i)
  rw [L.aeval_map_primaryIdempotent σ hσF hi] at h1
  exact h1

include L in
theorem LiftData.eRing_primaryProjectionR [DecidableEq (primaryFactors (idEnd x))]
    (i : primaryFactors (idEnd x)) :
    L.eRing (primaryProjectionR (idEnd x) (i : K[X])) =
      scalarPi (fun a : primaryFactors (idEnd x) => AdjoinRoot (a : K[X]))
        (fun a => primaryMultiplicity (idEnd x) (a : K[X])) (Pi.single i 1) := by
  funext j
  have hsq := L.squarefree_idEnd
  by_cases hji : j = i
  · subst hji
    have h1 : commutantEquivPi hsq (primaryProjectionR (idEnd x) (j : K[X])) j = 1 := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact primaryProjection_of_mem hsq j.2 v.2
    change LinearMap.toMatrixAlgEquiv (Module.finBasis _ _)
      (commutantEquivPi hsq (primaryProjectionR (idEnd x) (j : K[X])) j) = _
    rw [h1, map_one]
    simp
  · have h1 : commutantEquivPi hsq (primaryProjectionR (idEnd x) (i : K[X])) j = 0 := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact primaryProjection_of_mem_ne hsq i.2 j.2 (fun h => hji (Subtype.ext h)) v.2
    change LinearMap.toMatrixAlgEquiv (Module.finBasis _ _)
      (commutantEquivPi hsq (primaryProjectionR (idEnd x) (i : K[X])) j) = _
    rw [h1, map_zero]
    simp [Pi.single_eq_of_ne hji]

include L in
theorem LiftData.fixesIdempotents_of_proj [DecidableEq (primaryFactors (idEnd x))]
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} (hAle : A ≤ idStab x) (a : ↥A)
    (hproj : ∀ i ∈ primaryFactors (idEnd x),
      actEndHom (h := h) L.three_le L.four_le (a : MulAut (primeFormP h (idGram K n)))
        (primaryProjection (idEnd x) i) = primaryProjection (idEnd x) i) :
    L.FixesIdempotents hAle a := by
  intro i
  set ζ := centerZeta (K := fun a : primaryFactors (idEnd x) => AdjoinRoot (a : K[X]))
    (m := fun a => primaryMultiplicity (idEnd x) (a : K[X])) (R := ↥(idCommutant x))
    L.multiplicity_pos L.eRing with hζdef
  have h1 : ((ζ (Pi.single i 1) : Subring.center ↥(idCommutant x)) : ↥(idCommutant x)) =
      primaryProjectionR (idEnd x) (i : K[X]) := by
    have : ((ζ (Pi.single i 1) : Subring.center ↥(idCommutant x)) : ↥(idCommutant x)) =
        L.eRing.symm (scalarPi (fun a : primaryFactors (idEnd x) => AdjoinRoot (a : K[X]))
          (fun a => primaryMultiplicity (idEnd x) (a : K[X])) (Pi.single i 1)) := rfl
    rw [this, RingEquiv.symm_apply_eq]
    exact (L.eRing_primaryProjectionR i).symm
  have h2 : (centerRingAut ((L.actR.comp (Subgroup.inclusion hAle)) a)) (ζ (Pi.single i 1)) =
      ζ (Pi.single i 1) := by
    apply Subtype.ext
    rw [coe_centerRingAut, h1]
    apply Subtype.ext
    rw [MonoidHom.comp_apply, L.coe_actR]
    exact hproj i i.2
  change ζ.symm ((centerRingAut ((L.actR.comp (Subgroup.inclusion hAle)) a))
    (ζ (Pi.single i 1))) = Pi.single i 1
  rw [h2]
  exact RingEquiv.symm_apply_apply _ _

end Act

section Sigma

variable {ℓ f : ℕ} {K : Type*} [Field K]

theorem map_iterate_eq (σ : K ≃+* K) (N : ℕ) (hσ : σ ^ N = 1) (b : K[X]) :
    (Polynomial.map (σ : K →+* K))^[N] b = b := by
  have key : ∀ (n : ℕ) (b : K[X]), (Polynomial.map (σ : K →+* K))^[n] b =
      b.map ((σ ^ n : K ≃+* K) : K →+* K) := by
    intro n
    induction n with
    | zero => intro b; ext i; simp
    | succ n ih =>
      intro b
      rw [Function.iterate_succ_apply', ih]
      ext i
      simp [Polynomial.coeff_map, pow_succ']
  rw [key, hσ]
  ext i
  simp

theorem dualPoly_map_comm (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) (a : K[X]) :
    dualPoly h.bar (a.map (σ : K →+* K)) = (dualPoly h.bar a).map (σ : K →+* K) := by
  have hc : ∀ c : K, (σ : K →+* K) (h.bar c) = h.bar ((σ : K →+* K) c) := fun c => by
    simp only [h.bar_apply, map_pow]
  have h1 : (a.map (σ : K →+* K)).map h.bar = (a.map h.bar).map (σ : K →+* K) := by
    ext i
    simp [Polynomial.coeff_map, hc]
  have h2 : (σ : K →+* K) ((h.bar (a.coeff 0))⁻¹) = (h.bar ((σ : K →+* K) (a.coeff 0)))⁻¹ := by
    rw [map_inv₀, hc]
  unfold dualPoly
  rw [Polynomial.map_mul, Polynomial.map_C, map_reverse, ← h1, Polynomial.coeff_map, h2]

end Sigma

end CFSG.RankThree.PartOne.KCUnitaryModel
