module

public import CFSG.Sporadic.Fi24I301.Facts
public import Certificates.Certificate810306
public import Certificates.Certificate10132
public import Certificates.Certificate13693
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66RealFix
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Classes
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeC
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.GlueO23
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Fi24.Native CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (J)
open MulAction

section Elements

noncomputable abbrev dJ : CFSG.Sporadic.Fi24.J := xJ 0

theorem letterJC_mem (z : ℤ) : letterJC z ∈ fi24C := by
  unfold letterJC
  split_ifs
  · exact fi24Ca_mem
  · exact fi24C.inv_mem fi24Ca_mem
  · exact fi24Cb_mem
  · exact fi24C.inv_mem fi24Cb_mem

theorem wordG_letterJC_mem (w : List ℤ) : wordG letterJC w ∈ fi24C := by
  induction w with
  | nil => rw [wordG_nil]; exact fi24C.one_mem
  | cons z w ih => rw [wordG_cons]; exact fi24C.mul_mem (letterJC_mem z) ih

theorem xJ_mem (i : ℕ) : xJ i ∈ fi24C := fi24C.pow_mem (wordG_letterJC_mem _) 4

end Elements

section Facts

theorem rowFacts : RowFacts := Certificates.certificate810306

theorem xJ_pow_three {i : ℕ} (hi : i < 5) : xJ i ^ 3 = 1 := rowFacts.1 i hi

theorem xJ_comm {i j : ℕ} (hi : i < 5) (hj : j < 5) : xJ i * xJ j = xJ j * xJ i :=
  rowFacts.2.1 i hi j hj

theorem xJ_indep : ∀ i₀ i₁ i₂ i₃ i₄ : ℕ, i₀ < 3 → i₁ < 3 → i₂ < 3 → i₃ < 3 → i₄ < 3 →
    xJ 0 ^ i₀ * xJ 1 ^ i₁ * xJ 2 ^ i₂ * xJ 3 ^ i₃ * xJ 4 ^ i₄ = 1 →
      i₀ = 0 ∧ i₁ = 0 ∧ i₂ = 0 ∧ i₃ = 0 ∧ i₄ = 0 := rowFacts.2.2.1

theorem card_fixedBy_dJ : Nat.card (fixedBy (Fin 306936) dJ) = 3240 := rowFacts.2.2.2.1

theorem dJ_ne_one : dJ ≠ 1 := by
  intro h
  have h1 := card_fixedBy_dJ
  rw [h] at h1
  have h2 : fixedBy (Fin 306936) (1 : J) = Set.univ := by
    ext x
    simp
  rw [h2, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact absurd h1 (by norm_num)

theorem orderOf_dJ : orderOf dJ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (xJ_pow_three (by norm_num)) dJ_ne_one

theorem isConj_dJ :
    IsConj dJ (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.fi24Rep3 0) := by
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Sylow.fi24ThreeClasses_holds dJ orderOf_dJ
  obtain ⟨c, hc⟩ := isConj_iff.1 hi
  have hfix := CFSG.LocalAnalysis.GLTheoremA.CatB.card_fixedBy_conj (X := Fin 306936) c dJ
  rw [hc, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Sylow.card_fixedBy_fi24Rep3,
    card_fixedBy_dJ] at hfix
  have hi0 : i = 0 := by
    fin_cases i <;> simp_all [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Sylow.repFix]
  rw [hi0] at hi
  exact hi

end Facts

section Images

theorem fi24Rho_letterJC (z : ℤ) : fi24Rho ⟨letterJC z, letterJC_mem z⟩ = fi24KLetterG z := by
  by_cases h1 : z = 1
  · subst h1
    have e : (⟨letterJC 1, letterJC_mem 1⟩ : ↥fi24C) = ⟨fi24Ca, fi24Ca_mem⟩ :=
      Subtype.ext (by simp [letterJC])
    rw [e, fi24Rho_a]
    simp [fi24KLetterG]
  by_cases h2 : z = -1
  · subst h2
    have e : (⟨letterJC (-1), letterJC_mem (-1)⟩ : ↥fi24C) = (⟨fi24Ca, fi24Ca_mem⟩ : ↥fi24C)⁻¹ :=
      Subtype.ext (by simp [letterJC])
    rw [e, map_inv, fi24Rho_a]
    simp [fi24KLetterG]
  by_cases h3 : z = 2
  · subst h3
    have e : (⟨letterJC 2, letterJC_mem 2⟩ : ↥fi24C) = ⟨fi24Cb, fi24Cb_mem⟩ :=
      Subtype.ext (by simp [letterJC])
    rw [e, fi24Rho_b]
    simp [fi24KLetterG]
  · have e : (⟨letterJC z, letterJC_mem z⟩ : ↥fi24C) = (⟨fi24Cb, fi24Cb_mem⟩ : ↥fi24C)⁻¹ :=
      Subtype.ext (by simp [letterJC, h1, h2, h3])
    rw [e, map_inv, fi24Rho_b]
    simp [fi24KLetterG, h1, h2, h3]

theorem fi24Rho_wordG (w : List ℤ) :
    fi24Rho ⟨wordG letterJC w, wordG_letterJC_mem w⟩ = wordG fi24KLetterG w := by
  induction w with
  | nil =>
    have e : (⟨wordG letterJC [], wordG_letterJC_mem []⟩ : ↥fi24C) = 1 :=
      Subtype.ext (by simp [wordG_nil])
    rw [e, map_one, wordG_nil]
  | cons z w ih =>
    have e : (⟨wordG letterJC (z :: w), wordG_letterJC_mem (z :: w)⟩ : ↥fi24C) =
        ⟨letterJC z, letterJC_mem z⟩ * ⟨wordG letterJC w, wordG_letterJC_mem w⟩ :=
      Subtype.ext (by simp [wordG_cons])
    rw [e, map_mul, ih, wordG_cons, fi24Rho_letterJC]

theorem fi24Rho_xJ (i : ℕ) :
    fi24Rho ⟨xJ i, xJ_mem i⟩ = wordG fi24KLetterG genWords[i]! ^ 4 := by
  have e : (⟨xJ i, xJ_mem i⟩ : ↥fi24C) =
      (⟨wordG letterJC genWords[i]!, wordG_letterJC_mem _⟩ : ↥fi24C) ^ 4 :=
    Subtype.ext (by simp [xJ])
  rw [e, map_pow, fi24Rho_wordG]

theorem fi24KLetterG_eq : fi24KLetterG = kLet := by
  funext z
  rfl

end Images

section ImagesP

open CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem fi24Psi_xJ (i : ℕ) :
    fi24Psi ⟨xJ i, xJ_mem i⟩ = wordG fi24PLetterG genWords[i]! ^ 4 := by
  have h1 : fi24RhoK ⟨xJ i, xJ_mem i⟩ = fi24KW genWords[i]! ^ 4 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact fi24Rho_xJ i)
  show fi24Phi (fi24RhoK _) = _
  rw [h1, map_pow, fi24Phi_KW]

theorem fi24PLetterG_eq : fi24PLetterG = pLet := by
  funext z
  rfl

end ImagesP

end CFSG.Sporadic.Fi24I301
