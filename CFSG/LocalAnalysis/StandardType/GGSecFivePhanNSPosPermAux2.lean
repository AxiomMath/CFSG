module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType

open Matrix

theorem ggNSPosPA_monomial_of_conj_torus
    {K : Type} [Field K] [CharP K 2] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (ζ : Kˣ) (hζ : orderOf ζ = p) (x : GL (Fin n) K)
    (h : ∀ v : Fin n → ℕ, p ∣ ∑ i, v i →
      ∃ d : Fin n → K,
        (x : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => ((ζ : K) ^ (v i))) *
          ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d) :
    ∃ d : Fin n → Kˣ, ∃ σ : Equiv.Perm (Fin n),
      x = TauCeti.diagGL d * TauCeti.permutationGL σ := by
  classical
  have hp2le : 2 ≤ p := hp.two_le
  refine TauCeti.exists_eq_diagGL_mul_permutationGL_of_forall_ne ?_
  intro i j hij
  let v : Fin n → ℕ := fun k => (if k = i then 1 else 0) + (if k = j then p - 1 else 0)
  have hsum : ∑ k, v k = p := by
    have h1 : ∑ k, (if k = i then (1 : ℕ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' Finset.univ i (fun _ => 1)]; simp
    have h2 : ∑ k, (if k = j then (p - 1 : ℕ) else 0) = p - 1 := by
      rw [Finset.sum_ite_eq' Finset.univ j (fun _ => p - 1)]; simp
    simp only [v, Finset.sum_add_distrib, h1, h2]
    omega
  obtain ⟨d, hd⟩ := h v (by rw [hsum])
  let t : Fin n → Kˣ := fun k => ζ ^ (v k)
  have hmid : ((TauCeti.diagGL t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun i => (ζ : K) ^ (v i)) := by
    ext a b
    rw [TauCeti.diagGL_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp [t, Units.val_pow_eq_pow_val]
    · simp [hab]
  have hmem : x * TauCeti.diagGL t * x⁻¹ ∈ TauCeti.diagonalTorus K n := by
    rw [TauCeti.mem_diagonalTorus_iff]
    rw [show (((x * TauCeti.diagGL t * x⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i => (ζ : K) ^ (v i)) *
          ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) by
      rw [Units.val_mul, Units.val_mul, hmid]]
    rw [hd]
    exact Matrix.isDiag_diagonal d
  refine ⟨t, hmem, ?_⟩
  have hti : t i = ζ := by simp [t, v, hij]
  have htj : t j = ζ ^ (p - 1) := by simp [t, v, hij, Ne.symm hij]
  rw [hti, htj]
  intro hcon
  have hpow : ζ ^ (p - 2) = 1 := by
    have h1 : ζ ^ (p - 1) = ζ := hcon.symm
    rw [show p - 1 = (p - 2) + 1 by omega, pow_succ] at h1
    have h1' := congrArg (fun z => z * ζ⁻¹) h1
    simpa [mul_assoc] using h1'
  have hdvd : p ∣ p - 2 := by
    have h0 : orderOf ζ ∣ p - 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := ζ) (n := p - 2)).mpr hpow
    rwa [hζ] at h0
  have hzero : p - 2 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

end CFSG.StandardType

end
