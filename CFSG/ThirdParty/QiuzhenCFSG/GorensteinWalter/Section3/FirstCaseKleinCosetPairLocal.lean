module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-!
# Local commuting-pair bookkeeping for the first-case count

The external involutions in a non-base `Ĥ`-coset are written `h * y` with
`h ∈ I_Ĥ(y)`.  Two such involutions commute exactly when the quotient
`h₁ * h₂⁻¹` is itself an involution of `Ĥ`.  This module isolates that
purely group-theoretic translation; the per-coset distribution lemma that
uses it will be added next to `FirstCaseKleinCosetPairIncidence`.
-/

/-- For involutions `y` outside `H` and inverted elements `h₁, h₂ ∈ H`,
the external involutions `h₁ * y` and `h₂ * y` commute iff
`h₁ * h₂⁻¹` is an involution. -/
public theorem commute_external_involutions_iff_involution_difference
    {G : Type u} [Group G]
    (H : Subgroup G) {y h1 h2 : G}
    (hy : IsInvolution y)
    (_h1H : h1 ∈ H) (_h2H : h2 ∈ H)
    (h1inv : y * h1 * y⁻¹ = h1⁻¹)
    (h2inv : y * h2 * y⁻¹ = h2⁻¹)
    (hne : h1 ≠ h2) :
    Commute (h1 * y) (h2 * y) ↔ IsInvolution (h1 * h2⁻¹) := by
  classical
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyh1 : y * h1 * y = h1⁻¹ := by
    have h : y * h1 = h1⁻¹ * y := by
      have hh := congrArg (fun z : G => z * y) h1inv
      simpa [mul_assoc] using hh
    calc
      (y * h1) * y = (h1⁻¹ * y) * y := by rw [h]
      _ = h1⁻¹ := by rw [mul_assoc, hy2, mul_one]
  have hyh2 : y * h2 * y = h2⁻¹ := by
    have h : y * h2 = h2⁻¹ * y := by
      have hh := congrArg (fun z : G => z * y) h2inv
      simpa [mul_assoc] using hh
    calc
      (y * h2) * y = (h2⁻¹ * y) * y := by rw [h]
      _ = h2⁻¹ := by rw [mul_assoc, hy2, mul_one]
  have hprod12 : (h1 * y) * (h2 * y) = h1 * h2⁻¹ := by
    calc
      (h1 * y) * (h2 * y) = h1 * ((y * h2) * y) := by group
      _ = h1 * h2⁻¹ := by rw [hyh2]
  have hprod21 : (h2 * y) * (h1 * y) = h2 * h1⁻¹ := by
    calc
      (h2 * y) * (h1 * y) = h2 * ((y * h1) * y) := by group
      _ = h2 * h1⁻¹ := by rw [hyh1]
  have hdiffInv : (h1 * h2⁻¹)⁻¹ = h2 * h1⁻¹ := by
    rw [mul_inv_rev]
    simp
  constructor
  · intro hcomm
    have hEq : h1 * h2⁻¹ = h2 * h1⁻¹ := by
      calc
        h1 * h2⁻¹ = (h1 * y) * (h2 * y) := hprod12.symm
        _ = (h2 * y) * (h1 * y) := hcomm.eq
        _ = h2 * h1⁻¹ := hprod21
    have hdEq : h1 * h2⁻¹ = (h1 * h2⁻¹)⁻¹ := by
      calc
        h1 * h2⁻¹ = h2 * h1⁻¹ := hEq
        _ = (h1 * h2⁻¹)⁻¹ := hdiffInv.symm
    refine ⟨?_, ?_⟩
    · intro h1eq
      have h12 : h1 = h2 := by
        calc
          h1 = (h1 * h2⁻¹) * h2 := by group
          _ = 1 * h2 := by rw [h1eq]
          _ = h2 := by simp
      exact hne h12
    · rw [pow_two]
      have hdEq' : (h1 * h2⁻¹)⁻¹ = h1 * h2⁻¹ := hdEq.symm
      calc
        (h1 * h2⁻¹) * (h1 * h2⁻¹) = (h1 * h2⁻¹) * (h1 * h2⁻¹)⁻¹ := by
          rw [hdEq']
        _ = 1 := mul_inv_cancel (h1 * h2⁻¹)
  · intro hI
    have hdEq : h1 * h2⁻¹ = (h1 * h2⁻¹)⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hI.2)).symm
    rw [Commute]
    calc
      (h1 * y) * (h2 * y) = h1 * h2⁻¹ := hprod12
      _ = (h1 * h2⁻¹)⁻¹ := hdEq
      _ = h2 * h1⁻¹ := hdiffInv
      _ = (h2 * y) * (h1 * y) := hprod21.symm

end CFSG.GorensteinWalter
