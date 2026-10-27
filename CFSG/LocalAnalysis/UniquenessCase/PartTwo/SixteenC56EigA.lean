module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Diag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaEig

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

private theorem sum_range_succ_of_periodic {M : Type*} [AddCommGroup M] (g : ℕ → M) (p : ℕ)
    (h : g p = g 0) : ∑ j ∈ Finset.range p, g (j + 1) = ∑ j ∈ Finset.range p, g j := by
  have h1 := Finset.sum_range_succ g p
  have h2 := Finset.sum_range_succ' g p
  rw [h] at h1
  exact add_right_cancel (h2.symm.trans h1)

theorem pol_mulVec_of_similitude {A : Matrix OmI OmI K} {c : K}
    (hQ : ∀ v, quad (A *ᵥ v) = c * quad v) (v w : OmI → K) :
    pol (A *ᵥ v) (A *ᵥ w) = c * pol v w := by
  unfold pol
  rw [← Matrix.mulVec_add, hQ, hQ, hQ]
  ring

theorem eigen_decomp (A : GL OmI K) (hA : A ^ (Fintype.card K - 1) = 1)
    (R : Submodule K (OmI → K)) (hR : ∀ r ∈ R, (A : Matrix OmI OmI K) *ᵥ r ∈ R)
    {v : OmI → K} (hv : v ∈ R) :
    ∃ w : Kˣ → (OmI → K), (∀ ν, (A : Matrix OmI OmI K) *ᵥ w ν = (ν : K) • w ν) ∧
      (∀ ν, w ν ∈ R) ∧ ∑ ν, w ν = v := by
  classical
  have hAm : (A : Matrix OmI OmI K) ^ (Fintype.card K - 1) = 1 := by
    have h := Units.val_pow_eq_pow_val (a := A) (n := Fintype.card K - 1)
    rw [hA] at h
    simpa using h.symm
  let w : Kˣ → (OmI → K) := fun ν =>
    ∑ j ∈ Finset.range (Fintype.card K - 1),
      (((ν⁻¹ : Kˣ) : K) ^ j) • (((A : Matrix OmI OmI K) ^ j) *ᵥ v)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro ν
    have hνpow : (ν⁻¹ : Kˣ) ^ (Fintype.card K - 1) = 1 := by
      rw [← Fintype.card_units]
      exact pow_card_eq_one
    have hνK : (((ν⁻¹ : Kˣ) : K) ^ (Fintype.card K - 1)) = 1 := by
      simpa using congrArg (fun u : Kˣ => (u : K)) hνpow
    have hg : (fun k => (((ν⁻¹ : Kˣ) : K) ^ k) •
          (((A : Matrix OmI OmI K) ^ k) *ᵥ v)) (Fintype.card K - 1) =
        (fun k => (((ν⁻¹ : Kˣ) : K) ^ k) •
          (((A : Matrix OmI OmI K) ^ k) *ᵥ v)) 0 := by
      simp only [hνK, hAm, pow_zero, Matrix.one_mulVec, one_smul]
    simp only [w]
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    trans ∑ j ∈ Finset.range (Fintype.card K - 1),
        (ν : K) • ((((ν⁻¹ : Kˣ) : K) ^ (j + 1)) •
          (((A : Matrix OmI OmI K) ^ (j + 1)) *ᵥ v))
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      have hcoef : (ν : K) * (((ν⁻¹ : Kˣ) : K) ^ (j + 1)) = (((ν⁻¹ : Kˣ) : K) ^ j) := by
        rw [pow_succ', ← mul_assoc, Units.val_inv_eq_inv_val,
          mul_inv_cancel₀ (Units.ne_zero ν), one_mul]
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ', smul_smul, hcoef]
    · rw [← Finset.smul_sum, ← Finset.smul_sum]
      exact congrArg (fun x => (ν : K) • x)
        (sum_range_succ_of_periodic (fun k => (((ν⁻¹ : Kˣ) : K) ^ k) •
          (((A : Matrix OmI OmI K) ^ k) *ᵥ v)) (Fintype.card K - 1) hg)
  · intro ν
    have hpow : ∀ j, ((A : Matrix OmI OmI K) ^ j) *ᵥ v ∈ R := by
      intro j
      induction j with
      | zero => simpa using hv
      | succ j ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        exact hR _ ih
    simp only [w]
    exact Submodule.sum_smul_mem R (fun j => (((ν⁻¹ : Kˣ) : K) ^ j))
      (fun j _ => hpow j)
  · have hnpos : 0 < Fintype.card K - 1 := by
      have h2 : 1 < Fintype.card K := Fintype.one_lt_card
      omega
    have hS (j : ℕ) : (∑ ν : Kˣ, (((ν⁻¹ : Kˣ) : K) ^ j)) =
        ∑ ν : Kˣ, ((ν : K) ^ j) :=
      Equiv.sum_comp (Equiv.inv Kˣ) (fun ν : Kˣ => ((ν : K) ^ j))
    have hSval (j : ℕ) : (∑ ν : Kˣ, (((ν⁻¹ : Kˣ) : K) ^ j)) =
        if Fintype.card K - 1 ∣ j then -1 else 0 := by
      rw [hS j, FiniteField.sum_pow_units]
    simp only [w]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hSval]
    trans ∑ j ∈ Finset.range (Fintype.card K - 1),
        (if Fintype.card K - 1 ∣ j then (-1 : K) else 0) •
          (((A : Matrix OmI OmI K) ^ j) *ᵥ v)
    · rfl
    · rw [Finset.sum_eq_single 0]
      · rw [if_pos (dvd_zero _), pow_zero, Matrix.one_mulVec]
        rw [show (-1 : K) = 1 by rw [CharTwo.neg_eq (1 : K)], one_smul]
      · intro j hj hj0
        have hlt : j < Fintype.card K - 1 := Finset.mem_range.mp hj
        have hndvd : ¬ (Fintype.card K - 1) ∣ j :=
          fun h => hj0 (Nat.eq_zero_of_dvd_of_lt h hlt)
        rw [if_neg hndvd, zero_smul]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hnpos) hnot

theorem exists_dual_eigenvector (A : GL OmI K) (hA : A ^ (Fintype.card K - 1) = 1) {c : K}
    (hQ : ∀ v, quad ((A : Matrix OmI OmI K) *ᵥ v) = c * quad v) {e₀ : OmI → K} (he₀ : e₀ ≠ 0)
    (hfix : ∀ v, (A : Matrix OmI OmI K) *ᵥ v = v ↔ ∃ t : K, v = t • e₀) :
    c ≠ 0 ∧ c ≠ 1 ∧ ∃ f : OmI → K,
      (A : Matrix OmI OmI K) *ᵥ f = c • f ∧ pol e₀ f = 1 ∧ quad f = 0 := by
  classical
  have hc0 : c ≠ 0 := by
    intro hc
    have hquad_zero : ∀ w : OmI → K, quad w = 0 := by
      intro w
      obtain ⟨v, hv⟩ : ∃ v : OmI → K, (A : Matrix OmI OmI K) *ᵥ v = w :=
        ⟨((A⁻¹ : GL OmI K) : Matrix OmI OmI K) *ᵥ w, by
          simp [Matrix.mulVec_mulVec]⟩
      rw [← hv, hQ, hc, zero_mul]
    have h1 : quad (Pi.single (Sum.inl 0) (1 : K) + Pi.single (Sum.inr 0) (1 : K)) =
        (1 : K) := by
      simp [quad_eq]
    rw [hquad_zero _] at h1
    exact one_ne_zero h1.symm
  have he₀fix : (A : Matrix OmI OmI K) *ᵥ e₀ = e₀ := (hfix e₀).mpr ⟨1, by simp⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, pol e₀ v₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact he₀ (eq_zero_of_pol_eq_zero h)
  have hv₁ : pol e₀ ((pol e₀ v₀)⁻¹ • v₀) = 1 := by
    rw [pol_smul_right, inv_mul_cancel₀ hv₀]
  obtain ⟨w, hw_eig, _, hw_sum⟩ := eigen_decomp A hA (⊤ : Submodule K (OmI → K))
    (fun r _ => Submodule.mem_top) (v := (pol e₀ v₀)⁻¹ • v₀) Submodule.mem_top
  have hP : ∀ ν : Kˣ, ((ν : K) - c) * pol e₀ (w ν) = 0 := by
    intro ν
    have h := pol_mulVec_of_similitude (A := (A : Matrix OmI OmI K)) hQ e₀ (w ν)
    rw [he₀fix, hw_eig ν, pol_smul_right] at h
    have : (ν : K) * pol e₀ (w ν) - c * pol e₀ (w ν) = 0 := sub_eq_zero.mpr h
    rwa [← sub_mul] at this
  have hPzero : ∀ ν : Kˣ, (ν : K) ≠ c → pol e₀ (w ν) = 0 := fun ν hν =>
    (mul_eq_zero.mp (hP ν)).resolve_left (sub_ne_zero.mpr hν)
  have hsumP : (∑ ν : Kˣ, pol e₀ (w ν)) = 1 := by
    rw [← pol_sum_right e₀ Finset.univ w, hw_sum]
    exact hv₁
  have hPν₀ : pol e₀ (w (Units.mk0 c hc0)) = 1 := by
    have hsingle : (∑ ν : Kˣ, pol e₀ (w ν)) = pol e₀ (w (Units.mk0 c hc0)) :=
      Finset.sum_eq_single (Units.mk0 c hc0)
        (fun ν _ hν => hPzero ν (fun h => hν (Units.ext h)))
        (fun hnot => absurd (Finset.mem_univ _) hnot)
    rw [← hsingle, hsumP]
  have hval : ((Units.mk0 c hc0 : Kˣ) : K) = c := Units.val_mk0 hc0
  have hf : (A : Matrix OmI OmI K) *ᵥ w (Units.mk0 c hc0) = c • w (Units.mk0 c hc0) := by
    rw [hw_eig (Units.mk0 c hc0), hval]
  have hc1 : c ≠ 1 := by
    intro hc1
    have hfixf : (A : Matrix OmI OmI K) *ᵥ w (Units.mk0 c hc0) = w (Units.mk0 c hc0) := by
      have hsmul : c • w (Units.mk0 c hc0) = (1 : K) • w (Units.mk0 c hc0) :=
        congrArg (fun x : K => x • w (Units.mk0 c hc0)) hc1
      rw [hf, hsmul, one_smul]
    obtain ⟨t, ht⟩ := (hfix _).mp hfixf
    have h0 : pol e₀ (w (Units.mk0 c hc0)) = 0 := by
      rw [ht, pol_smul_right, pol_self, mul_zero]
    rw [hPν₀] at h0
    exact one_ne_zero h0
  refine ⟨hc0, hc1, w (Units.mk0 c hc0), hf, hPν₀, ?_⟩
  have h1 : c * quad (w (Units.mk0 c hc0)) = c ^ 2 * quad (w (Units.mk0 c hc0)) := by
    rw [← hQ (w (Units.mk0 c hc0)), hf, quad_smul]
  have h2 : (c - c ^ 2) * quad (w (Units.mk0 c hc0)) = 0 := by
    rw [sub_mul, h1, sub_self]
  have hcne : c - c ^ 2 ≠ 0 := by
    have h : c - c ^ 2 = c * (1 - c) := by ring
    rw [h]
    exact mul_ne_zero hc0 (sub_ne_zero.mpr (Ne.symm hc1))
  exact (mul_eq_zero.mp h2).resolve_left hcne

end OmegaEig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
