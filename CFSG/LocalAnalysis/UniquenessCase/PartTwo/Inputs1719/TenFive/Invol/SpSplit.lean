module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpCases

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)

variable {r : ℕ} {K : Type} [Field K]

private lemma spForm_smul_left (s : K) (y z : Fin r ⊕ Fin r → K) :
    spForm (s • y) z = s * spForm y z := by
  rw [spForm, spForm, smul_dotProduct, smul_eq_mul]

private lemma spForm_smul_right (t : K) (y z : Fin r ⊕ Fin r → K) :
    spForm y (t • z) = t * spForm y z := by
  rw [spForm, spForm, mulVec_smul, dotProduct_smul, smul_eq_mul]

private lemma spForm_smul (s t : K) (y z : Fin r ⊕ Fin r → K) :
    spForm (s • y) (t • z) = s * t * spForm y z := by
  rw [spForm_smul_left, spForm_smul_right]
  ring

private lemma spT_smul (s t : K) (a c : Fin r ⊕ Fin r → K) :
    spT (t • c) (s • a) = (s * t) • spT c a := by
  ext i k
  simp only [spT, vecMulVec, Matrix.mulVec_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply]
  ring

private lemma spN_smul (s t : K) (a c : Fin r ⊕ Fin r → K) :
    spN (s • a) (t • c) = (s * t) • spN a c := by
  rw [spN, spN, smul_add, spT_smul s t a c, spT_smul t s c a, mul_comm t s]

private lemma exists_mulVec_ne_zero {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : M ≠ 0) : ∃ y : Fin r ⊕ Fin r → K, M *ᵥ y ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [h (Pi.single j 1), Matrix.zero_mulVec]

theorem exists_spN_inv_split (h2 : (2 : K) ≠ 0) (A : GL (Fin r ⊕ Fin r) K) {c : K}
    (hA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K * A = c ^ 2 • formJ r K)
    (hd : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * A = c ^ 2 • 1)
    (hAs : ∀ a : K, (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ≠ a • 1) :
    ∃ v u : Fin r ⊕ Fin r → K, v ≠ 0 ∧ u ≠ 0 ∧ spForm v u = 0 ∧
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * spN v u *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          -spN v u := by
  classical
  have hc : c ≠ 0 := by
    intro hc0
    apply hAs 0
    have hAA : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 0 := by
      rw [hd, hc0]
      simp
    have hAinv : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
      simp
    calc (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * 1 := (mul_one _).symm
      _ = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
          ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
            ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) := by
            rw [hAinv]
      _ = ((A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
            (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *
            ((A⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
            rw [Matrix.mul_assoc]
      _ = 0 := by rw [hAA, Matrix.zero_mul]
      _ = (0 : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by simp
  set B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    c⁻¹ • (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hBdef
  have hcB : c • B = (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    rw [hBdef, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hB2 : B * B = 1 := by
    rw [hBdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, smul_smul]
    rw [show (c⁻¹ * c⁻¹) * c ^ 2 = 1 by field_simp]
    simp
  have hB1 : B ≠ 1 := by
    intro h
    apply hAs c
    rw [← hcB, h]
  have hBneg : B ≠ -1 := by
    intro h
    apply hAs (-c)
    rw [← hcB, h]
    simp
  have h1B : (1 + B) ≠ 0 := by
    intro h
    apply hBneg
    exact neg_eq_iff_eq_neg.mp (eq_neg_of_add_eq_zero_left h).symm
  have h1mB : (1 - B) ≠ 0 := by
    intro h
    apply hB1
    exact (sub_eq_zero.mp h).symm
  obtain ⟨y, hy⟩ := exists_mulVec_ne_zero h1B
  obtain ⟨y', hy'⟩ := exists_mulVec_ne_zero h1mB
  set v : Fin r ⊕ Fin r → K := (1 + B) *ᵥ y with hvdef
  set u : Fin r ⊕ Fin r → K := (1 - B) *ᵥ y' with hudef
  have hv : v ≠ 0 := by rw [hvdef]; exact hy
  have hu : u ≠ 0 := by rw [hudef]; exact hy'
  have hB1B : B * (1 + B) = 1 + B := by
    rw [Matrix.mul_add, Matrix.mul_one, hB2]
    exact add_comm B 1
  have hB1mB : B * (1 - B) = -(1 - B) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hB2, neg_sub]
  have hBv : B *ᵥ v = v := by
    rw [hvdef, Matrix.mulVec_mulVec, hB1B]
  have hBu : B *ᵥ u = -u := by
    rw [hudef, Matrix.mulVec_mulVec, hB1mB, Matrix.neg_mulVec]
  have hAv : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = c • v := by
    rw [← hcB, Matrix.smul_mulVec, hBv]
  have hAu : (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u = (-c) • u := by
    rw [← hcB, Matrix.smul_mulVec, hBu, smul_neg, neg_smul]
  have hvu : spForm v u = 0 := by
    have h1 := spForm_mulVec (A := (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hA v u
    rw [hAv, hAu, spForm_smul c (-c) v u] at h1
    have hcoef : c * (-c) = -(c ^ 2) := by ring
    rw [hcoef] at h1
    have h' : -(c ^ 2 * spForm v u) = c ^ 2 * spForm v u := by
      simpa [neg_mul] using h1
    have h2c : (2 : K) * c ^ 2 ≠ 0 := mul_ne_zero h2 (pow_ne_zero 2 hc)
    have hzero : (2 * c ^ 2) * spForm v u = 0 := by
      calc (2 * c ^ 2) * spForm v u = c ^ 2 * spForm v u + c ^ 2 * spForm v u := by ring
        _ = -(c ^ 2 * spForm v u) + c ^ 2 * spForm v u := by rw [h']
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp hzero).resolve_left h2c
  have hinv := conj_spN (A : GL (Fin r ⊕ Fin r) K) hA v u
  rw [hAv, hAu, spN_smul c (-c) v u, smul_smul] at hinv
  have hcoef : (c ^ 2)⁻¹ * (c * (-c)) = -1 := by
    rw [show c * (-c) = -(c ^ 2) by ring]
    field_simp
  rw [hcoef, neg_one_smul] at hinv
  exact ⟨v, u, hv, hu, hvu, hinv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
