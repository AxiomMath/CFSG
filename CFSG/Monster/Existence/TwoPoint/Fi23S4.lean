
module

public import CFSG.Monster.Existence.TwoPoint.Fi23S4Base

public import CFSG.Monster.Existence.TwoPoint.Fi23S4Comm
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Cube
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Conj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess

theorem s4PowCheck_parts :
    wordLin s4WGamma * wordLin s4WGamma = 1 ∧ wordLin fiWU[8]! * wordLin fiWU[8]! = 1 ∧
      wordLin fiWBeta * wordLin s4WGamma = wordLin s4WGamma * wordLin fiWBeta ∧
      wordLin s4WE8Gamma ^ 3 = 1 ∧ wordLin s4WAlphaGamma ^ 3 = 1 ∧
      wordLin s4WE8Gamma ≠ 1 ∧ wordLin s4WAlphaGamma ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := s4PowCheck_ok
  rw [wordLin_append] at h1 h2
  rw [wordLin_append, wordLin_append] at h3 h4 h5
  refine ⟨h1, h2, h3, ?_, ?_, h6, h7⟩
  · rw [← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  · rw [← h5]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem gammaZero_mul_self :
    gammaZero * gammaZero = 1 :=
  Subtype.ext s4PowCheck_parts.1

theorem fiE_eight_mul_self :
    fiE 8 * fiE 8 = 1 :=
  Subtype.ext s4PowCheck_parts.2.1

theorem s4_conj_gammaZero :
    fiMkW s4CGamma * tGriess * (fiMkW s4CGamma)⁻¹ = gammaZero := by
  have h := (s4ConjCheck_parts s4ConjCheck_ok).1
  have h' : fiMkW s4CGamma * tGriess = gammaZero * fiMkW s4CGamma := by
    rw [← fiMkW_fiRhoT]
    exact Subtype.ext h
  rw [h', mul_inv_cancel_right]

theorem isConj_gammaZero :
    IsConj tGriess gammaZero := isConj_iff.2 ⟨_, s4_conj_gammaZero⟩

theorem fiE_commute_gammaZero
    {i : ℕ} (hi : i < 10) (hi8 : i ≠ 8) :
    fiE i * gammaZero = gammaZero * fiE i := by
  have hmem : i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h := s4CommGenCheck_ok i hmem
  rw [wordLin_append, wordLin_append] at h
  exact Subtype.ext h

theorem fiBeta_commute_gammaZero :
    fiBeta * gammaZero = gammaZero * fiBeta :=
  Subtype.ext s4PowCheck_parts.2.2.1

theorem isConj_fiBeta_mul_gammaZero :
    IsConj tGriess (fiBeta * gammaZero) := by
  have h := (s4ConjCheck_parts s4ConjCheck_ok).2
  have e : fiBeta * gammaZero = fiMkW s4WBetaGamma := (fiMkW_append s4WGamma fiWBeta).symm
  have h' : fiMkW s4CBetaGamma * tGriess = fiBeta * gammaZero * fiMkW s4CBetaGamma := by
    rw [e, ← fiMkW_fiRhoT]
    exact Subtype.ext h
  exact isConj_iff.2 ⟨fiMkW s4CBetaGamma, by rw [h', mul_inv_cancel_right]⟩

theorem fiE_eight_mul_gammaZero_pow_three :
    (fiE 8 * gammaZero) ^ 3 = 1 := by
  rw [fiE_eight_mul_gammaZero_eq]
  exact Subtype.ext s4PowCheck_parts.2.2.2.1

theorem fiE_eight_mul_gammaZero_ne_one :
    fiE 8 * gammaZero ≠ 1 := by
  rw [fiE_eight_mul_gammaZero_eq]
  intro h
  exact s4PowCheck_parts.2.2.2.2.2.1 (fiMkW_eq_one_iff.1 h)

theorem fiAlpha_mul_gammaZero_pow_three :
    (fiAlpha * gammaZero) ^ 3 = 1 := by
  rw [fiAlpha_mul_gammaZero_eq]
  exact Subtype.ext s4PowCheck_parts.2.2.2.2.1

theorem fiAlpha_mul_gammaZero_ne_one :
    fiAlpha * gammaZero ≠ 1 := by
  rw [fiAlpha_mul_gammaZero_eq]
  intro h
  exact s4PowCheck_parts.2.2.2.2.2.2 (fiMkW_eq_one_iff.1 h)

theorem fiE_eight_not_commute_gammaZero :
    fiE 8 * gammaZero ≠ gammaZero * fiE 8 := by
  intro h
  have h2 : (fiE 8 * gammaZero) * (fiE 8 * gammaZero) = 1 :=
    calc (fiE 8 * gammaZero) * (fiE 8 * gammaZero) = fiE 8 * (gammaZero * fiE 8) * gammaZero := by
          simp only [mul_assoc]
      _ = fiE 8 * (fiE 8 * gammaZero) * gammaZero := by rw [← h]
      _ = (fiE 8 * fiE 8) * (gammaZero * gammaZero) := by simp only [mul_assoc]
      _ = 1 := by rw [fiE_eight_mul_self, gammaZero_mul_self, one_mul]
  have h3 : (fiE 8 * gammaZero) ^ 3 = fiE 8 * gammaZero := by
    rw [pow_succ, sq, h2, one_mul]
  exact fiE_eight_mul_gammaZero_ne_one (by rw [← h3]; exact fiE_eight_mul_gammaZero_pow_three)

theorem exists_s4_gamma :
    ∃ γ₀ : MGriess, γ₀ * γ₀ = 1 ∧ IsConj tGriess γ₀ ∧
      (∀ i, i < 10 → i ≠ 8 → fiE i * γ₀ = γ₀ * fiE i) ∧
      (fiE 8 * γ₀) ^ 3 = 1 ∧ fiE 8 * γ₀ ≠ 1 ∧ fiE 8 * γ₀ ≠ γ₀ * fiE 8 ∧
      (fiAlpha * γ₀) ^ 3 = 1 ∧ fiAlpha * γ₀ ≠ 1 ∧
      fiBeta * γ₀ = γ₀ * fiBeta ∧ IsConj tGriess (fiBeta * γ₀) :=
  ⟨gammaZero, gammaZero_mul_self, isConj_gammaZero, fun _ hi hi8 => fiE_commute_gammaZero hi hi8,
    fiE_eight_mul_gammaZero_pow_three, fiE_eight_mul_gammaZero_ne_one,
    fiE_eight_not_commute_gammaZero, fiAlpha_mul_gammaZero_pow_three,
    fiAlpha_mul_gammaZero_ne_one, fiBeta_commute_gammaZero, isConj_fiBeta_mul_gammaZero⟩

end CFSG.Monster.Existence
