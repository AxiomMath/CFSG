module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmClass
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import Mathlib

public section

open Module Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial isometryUnit isometryUnit_val
  isometryUnit_inv_val)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]
  {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]

theorem exists_ker_pow_neg_of_reciprocal (c : D ≃ₗ[K] D) (hcp : c ^ p = 1) {h : K[X]}
    (h0 : h.coeff 0 ≠ 0) {e : ZMod p}
    (hker : ∃ d : D, d ≠ 0 ∧
      aeval ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) (reciprocalPolynomial h) d = 0) :
    ∃ d : D, d ≠ 0 ∧ aeval ((c ^ (-e).val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0 := by
  obtain ⟨d, hd, hker⟩ := hker
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinv : (c ^ e.val : D ≃ₗ[K] D)⁻¹ = c ^ (-e).val := by
    refine mul_eq_one_iff_inv_eq.mp ?_
    rw [← pow_add]
    have hdvd : p ∣ e.val + (-e).val := by
      refine (ZMod.natCast_eq_zero_iff (e.val + (-e).val) p).mp ?_
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact add_neg_cancel e
    have hlt : e.val + (-e).val < 2 * p := by
      have h1 := ZMod.val_lt e
      have h2 := ZMod.val_lt (-e)
      omega
    obtain ⟨k, hk⟩ := hdvd
    have hklt : k < 2 := by
      have hp : 0 < p := (Fact.out : p.Prime).pos
      have h := hlt
      rw [hk, Nat.mul_comm 2 p] at h
      exact (Nat.mul_lt_mul_left hp).mp h
    interval_cases k
    · rw [hk, Nat.mul_zero, pow_zero]
    · rw [hk, Nat.mul_one, hcp]
  refine ⟨d, hd, ?_⟩
  have hrec := CFSG.RankThree.PartOne.KCOrthogonal.aeval_reciprocalPolynomial_of_unit
    (isometryUnit (c ^ e.val : D ≃ₗ[K] D)) h
  rw [isometryUnit_val, isometryUnit_inv_val] at hrec
  rw [hrec] at hker
  simp only [LinearMap.smul_apply, Module.End.mul_apply, smul_eq_zero, inv_eq_zero, h0,
    false_or] at hker
  have hinj : Function.Injective ((c ^ e.val : D ≃ₗ[K] D).toLinearMap ^ h.natDegree) := by
    rw [← CFSG.RankThree.PartOne.KCOrthogonal.toLinearMap_pow]
    exact ((c ^ e.val : D ≃ₗ[K] D) ^ h.natDegree).injective
  have hzero : aeval ((c ^ e.val : D ≃ₗ[K] D).symm).toLinearMap h d = 0 :=
    (map_eq_zero_iff _ hinj).mp hker
  have hs : ((c ^ e.val : D ≃ₗ[K] D).symm : D →ₗ[K] D) =
      ((c ^ (-e).val : D ≃ₗ[K] D) : D →ₗ[K] D) := by
    rw [← hinv]
    rfl
  rwa [hs] at hzero

theorem eq_or_eq_neg_of_ker_or_reciprocal_ker (hp2 : p ≠ 2) (c : D ≃ₗ[K] D)
    (hdim : finrank K D = 2) (hcp : c ^ p = 1) (hfix : ∀ u, c u = u → u = 0)
    (hT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹)
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (c x) = (c ^ e.val) (θ x)) → e = 1 ∨ e = -1)
    {h : K[X]} (hh : Irreducible h) (hX : h ≠ X - 1) (h0 : h.coeff 0 ≠ 0) {e e' : ZMod p}
    (he : e ≠ 0) (he' : e' ≠ 0)
    (h1 : (∃ d : D, d ≠ 0 ∧ aeval ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0) ∨
      (∃ d : D, d ≠ 0 ∧
        aeval ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) (reciprocalPolynomial h) d = 0))
    (h2 : (∃ d : D, d ≠ 0 ∧ aeval ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0) ∨
      (∃ d : D, d ≠ 0 ∧
        aeval ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) (reciprocalPolynomial h) d = 0)) :
    e' = e ∨ e' = -e := by
  rcases h1 with k1 | k1 <;> rcases h2 with k2 | k2
  · exact blockClass hp2 c hdim hcp hfix hT hroots hh hX he he' k1 k2
  · have k2' := exists_ker_pow_neg_of_reciprocal c hcp h0 k2
    rcases blockClass hp2 c hdim hcp hfix hT hroots hh hX he (neg_ne_zero.mpr he') k1 k2'
      with h | h
    · exact Or.inr (neg_eq_iff_eq_neg.mp h)
    · exact Or.inl (neg_inj.mp h)
  · have k1' := exists_ker_pow_neg_of_reciprocal c hcp h0 k1
    rcases blockClass hp2 c hdim hcp hfix hT hroots hh hX (neg_ne_zero.mpr he) he' k1' k2
      with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      calc e' = - -e := h
        _ = e := neg_neg e
  · have k1' := exists_ker_pow_neg_of_reciprocal c hcp h0 k1
    have k2' := exists_ker_pow_neg_of_reciprocal c hcp h0 k2
    rcases blockClass hp2 c hdim hcp hfix hT hroots hh hX (neg_ne_zero.mpr he)
      (neg_ne_zero.mpr he') k1' k2' with h | h
    · exact Or.inl (neg_inj.mp h)
    · refine Or.inr ?_
      calc e' = -(- -e) := neg_eq_iff_eq_neg.mp h
        _ = -e := congrArg (fun x : ZMod p => -x) (neg_neg e)

end OrthTorus

end CFSG.StandardType

end
