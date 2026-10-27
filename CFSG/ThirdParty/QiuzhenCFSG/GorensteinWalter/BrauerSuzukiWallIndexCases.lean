module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallPairCountPairings
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCharacterValues
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallIndexProductArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDegreeArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallHall
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallLinearCharacters
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallSignedDegree
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The two index cases in the Brauer--Suzuki--Wall argument

This module performs Bender's character comparison from
`refs/bender-bsw.tex`, lines 129--212.  The direct pair-count pairings and
Suzuki's irreducible expansion determine the character values at the
distinguished involution and then the two possible values of `|G : H|`.
-/

namespace CFSG.GorensteinWalter

noncomputable section

universe u

open Theory.Character
open BenderGlauberman

attribute [local instance] Fintype.ofFinite

/-- If `4 < |K|`, Bender's character calculation forces the two possible
values of the index of the involution centralizer. -/
public theorem BrauerSuzukiWallHypotheses.index_cases
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) :
    h.H.index =
        (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∨
      h.H.index =
        (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) := by
  classical
  obtain ⟨rhoHom, sigmaHom, hrho, hsigma, hrhoT, hsigmaT,
      hrhoSq, hsigmaSq⟩ := h.exists_linearCharacters_of_four_lt_card_K hk
  let rho : ClassFunction h.K := LambdaChar rhoHom
  let sigma : ClassFunction h.K := LambdaChar sigmaHom
  change IsLinearCharacter rho at hrho
  change IsLinearCharacter sigma at hsigma
  change rho ⟨h.t, h.t_mem_K⟩ = 1 at hrhoT
  change sigma ⟨h.t, h.t_mem_K⟩ = -1 at hsigmaT
  have hnotFixed (chi : h.K →* ℂˣ) (hchiSq : chi ^ 2 ≠ 1) :
      ¬ ∀ x : h.K, LambdaChar chi x⁻¹ = LambdaChar chi x := by
    intro hfix
    apply hchiSq
    apply MonoidHom.ext
    intro x
    have hunit : chi x⁻¹ = chi x := Units.ext (hfix x)
    have hxmul : chi x * chi x = 1 := by
      nth_rw 1 [← hunit]
      rw [map_inv]
      exact inv_mul_cancel (chi x)
    simpa [pow_two] using hxmul
  have hrhoNot : ¬ ∀ x : h.K, rho x⁻¹ = rho x := by
    simpa [rho] using hnotFixed rhoHom hrhoSq
  have hsigmaNot : ¬ ∀ x : h.K, sigma x⁻¹ = sigma x := by
    simpa [sigma] using hnotFixed sigmaHom hsigmaSq
  let hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  let alpha : ClassFunction h.H :=
    inducedFromSub hKleH ((1 : ClassFunction h.K) - rho)
  let beta : ClassFunction h.H :=
    inducedFromSub hKleH (rho - sigma)
  let alphaStar : ClassFunction G := Section1.inducedCF h.H alpha
  let betaStar : ClassFunction G := Section1.inducedCF h.H beta
  have htrans := h.transferred_character_relations
    hrho hsigma hrhoNot hsigmaNot hrhoT hsigmaT
  change IsVirtualCharacter alphaStar ∧
      IsVirtualCharacter betaStar ∧
      (∀ (x : G) (hx : x ∈ h.K), x ≠ 1 →
        alphaStar x = alpha ⟨x, hKleH hx⟩ ∧
          betaStar x = beta ⟨x, hKleH hx⟩) ∧
      alphaStar 1 = 0 ∧ betaStar 1 = 0 ∧
      alphaStar h.t = 0 ∧ betaStar h.t = 4 ∧
      Section1.scalarProduct G alphaStar alphaStar = 3 ∧
      Section1.scalarProduct G betaStar betaStar = 2 ∧
      Section1.scalarProduct G alphaStar betaStar = -1 ∧
      Section1.scalarProduct G alphaStar
          (Section1.principalCharacter G) = 1 ∧
      Section1.scalarProduct G betaStar
          (Section1.principalCharacter G) = 0 at htrans
  rcases htrans with
    ⟨halphaVirtual, hbetaVirtual, _hvalues,
      halphaOne, hbetaOne, halphaT, hbetaT,
      halphaNorm, hbetaNorm, halphaBeta,
      halphaPrincipal, hbetaPrincipal⟩
  obtain ⟨gamma, lambda, phi,
      hgammaSigned, hlambdaSigned, hphiSigned,
      _hgammaPrincipal, _hlambdaPrincipal, _hphiPrincipal,
      _hgammaLambda, _hgammaPhi, _hlambdaPhi,
      halphaDecomp, hbetaDecomp⟩ :=
    brauerSuzukiWall_character_decomposition
      halphaVirtual hbetaVirtual halphaNorm hbetaNorm halphaBeta
      halphaPrincipal hbetaPrincipal
  have hpairs := h.pairCount_pairings
    hrho hsigma hrhoNot hsigmaNot hrhoT hsigmaT
  change Section1.scalarProduct G alphaStar (bswPairCountClassFunction G) =
        (Nat.card h.K : ℂ) ∧
      Section1.scalarProduct G betaStar (bswPairCountClassFunction G) = 0
    at hpairs
  rcases hpairs with ⟨halphaPair, hbetaPair⟩
  let factor : ℂ :=
    (Nat.card G : ℂ) / (Nat.card h.H : ℂ) ^ 2
  have hGcardNe : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hHcardNe : (Nat.card h.H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := h.H)).ne'
  have hfactorNe : factor ≠ 0 := by
    exact div_ne_zero hGcardNe (pow_ne_zero 2 hHcardNe)
  have hformula := (h.pairCount_character_formula).2
  have hformulaGamma :
      Section1.scalarProduct G gamma (bswPairCountClassFunction G) =
        factor * (gamma h.t ^ 2 / gamma 1) := by
    simpa [factor] using hformula gamma hgammaSigned
  have hformulaLambda :
      Section1.scalarProduct G lambda (bswPairCountClassFunction G) =
        factor * (lambda h.t ^ 2 / lambda 1) := by
    simpa [factor] using hformula lambda hlambdaSigned
  have hformulaPhi :
      Section1.scalarProduct G phi (bswPairCountClassFunction G) =
        factor * (phi h.t ^ 2 / phi 1) := by
    simpa [factor] using hformula phi hphiSigned
  have hprincipalSigned :
      Section3.IsSignedIrreducibleCharacter
        (Section1.principalCharacter G) := by
    refine ⟨1, Or.inl rfl, Section1.principalCharacter G,
      Section3.principalCharacter_isIrreducibleCharacterOnGroup, ?_⟩
    simp
  have hformulaPrincipal :
      Section1.scalarProduct G (Section1.principalCharacter G)
          (bswPairCountClassFunction G) = factor := by
    have hp := hformula (Section1.principalCharacter G) hprincipalSigned
    simpa [factor, Section1.principalCharacter_apply] using hp
  have hbetaPairEq :
      Section1.scalarProduct G phi (bswPairCountClassFunction G) =
        Section1.scalarProduct G gamma (bswPairCountClassFunction G) := by
    rw [hbetaDecomp, Section5.scalarProduct_sub_left] at hbetaPair
    exact sub_eq_zero.mp hbetaPair
  rw [hformulaPhi, hformulaGamma] at hbetaPairEq
  have hratio : phi h.t ^ 2 / phi 1 = gamma h.t ^ 2 / gamma 1 :=
    mul_left_cancel₀ hfactorNe hbetaPairEq
  obtain ⟨gammaDegree, hgammaDegreeNe, hgammaOne⟩ :=
    signedIrreducibleCharacter_degree_int hgammaSigned
  obtain ⟨lambdaDegree, hlambdaDegreeNe, hlambdaOne⟩ :=
    signedIrreducibleCharacter_degree_int hlambdaSigned
  have hgammaOneNe : gamma 1 ≠ 0 := by
    rw [hgammaOne]
    exact_mod_cast hgammaDegreeNe
  obtain ⟨_hphiT, hgammaT, hlambdaT⟩ :=
    brauerSuzukiWall_character_values_of_square_ratio
      halphaT hbetaOne hbetaT halphaDecomp hbetaDecomp
      hgammaOneNe hratio
  have halphaComparison :
      (Nat.card h.K : ℂ) =
        factor *
          (1 + gamma h.t ^ 2 / gamma 1 -
            lambda h.t ^ 2 / lambda 1) := by
    calc
      (Nat.card h.K : ℂ) =
          Section1.scalarProduct G alphaStar
            (bswPairCountClassFunction G) := halphaPair.symm
      _ = Section1.scalarProduct G
          (Section1.principalCharacter G + gamma - lambda)
          (bswPairCountClassFunction G) := by rw [halphaDecomp]
      _ = Section1.scalarProduct G (Section1.principalCharacter G)
            (bswPairCountClassFunction G) +
          Section1.scalarProduct G gamma (bswPairCountClassFunction G) -
          Section1.scalarProduct G lambda
            (bswPairCountClassFunction G) := by
        rw [Section5.scalarProduct_sub_left,
          Section1.scalarProduct_add_left]
      _ = factor *
          (1 + gamma h.t ^ 2 / gamma 1 -
            lambda h.t ^ 2 / lambda 1) := by
        rw [hformulaPrincipal, hformulaGamma, hformulaLambda]
        ring
  have hGroupCardCast :
      (Nat.card G : ℂ) =
        (Nat.card h.H : ℂ) * (h.H.index : ℂ) := by
    exact_mod_cast h.H.card_mul_index.symm
  have hkCNe : (Nat.card h.K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := h.K)).ne'
  have hHCardCast :
      (Nat.card h.H : ℂ) = 2 * (Nat.card h.K : ℂ) := by
    exact_mod_cast h.card_H
  have hfactorEq :
      factor = (h.H.index : ℂ) / (2 * (Nat.card h.K : ℂ)) := by
    dsimp [factor]
    rw [hGroupCardCast, hHCardCast]
    field_simp [hkCNe]
  rw [hfactorEq, hgammaT, hlambdaT, hgammaOne, hlambdaOne] at halphaComparison
  norm_num at halphaComparison
  rw [← Nat.card_eq_fintype_card] at halphaComparison
  have hgammaDegreeCNe : (gammaDegree : ℂ) ≠ 0 := by
    exact_mod_cast hgammaDegreeNe
  have hlambdaDegreeCNe : (lambdaDegree : ℂ) ≠ 0 := by
    exact_mod_cast hlambdaDegreeNe
  have hmainC :
      2 * (Nat.card h.K : ℂ) ^ 2 * (gammaDegree : ℂ) *
          (lambdaDegree : ℂ) =
        (h.H.index : ℂ) *
          ((gammaDegree : ℂ) * (lambdaDegree : ℂ) +
            4 * (lambdaDegree : ℂ) - (gammaDegree : ℂ)) := by
    field_simp [hkCNe, hgammaDegreeCNe, hlambdaDegreeCNe] at halphaComparison
    ring_nf at halphaComparison ⊢
    exact halphaComparison
  have hdegreeC :
      (1 : ℂ) + (gammaDegree : ℂ) - (lambdaDegree : ℂ) = 0 := by
    have heval := congrFun halphaDecomp (1 : G)
    rw [halphaOne] at heval
    simp only [Pi.add_apply, Pi.sub_apply,
      Section1.principalCharacter_apply] at heval
    rw [hgammaOne, hlambdaOne] at heval
    exact heval.symm
  have hdegreeInt : 1 + gammaDegree - lambdaDegree = 0 := by
    exact_mod_cast hdegreeC
  have hmainInt :
      2 * (Nat.card h.K : ℤ) ^ 2 * gammaDegree * lambdaDegree =
        (h.H.index : ℤ) *
          (gammaDegree * lambdaDegree + 4 * lambdaDegree - gammaDegree) := by
    exact_mod_cast hmainC
  let tK : h.K := ⟨h.t, h.t_mem_K⟩
  have htKne : tK ≠ 1 := by
    intro htKone
    exact h.t_involution.1 (congrArg Subtype.val htKone)
  have htKsq : tK ^ 2 = 1 := by
    apply Subtype.ext
    exact h.t_involution.2
  have htKorder : orderOf tK = 2 :=
    orderOf_eq_prime htKsq htKne
  have hKeven : Even (Nat.card h.K) := by
    rw [even_iff_two_dvd, ← htKorder]
    exact orderOf_dvd_natCard tK
  have hindexPos : 0 < h.H.index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := h.H))
  have hcop := h.hall_H
  rw [h.card_H] at hcop
  have hindexProduct :
      2 * (h.H.index : ℤ) = gammaDegree * lambdaDegree :=
    brauerSuzukiWall_index_product_of_degree_equation
      (Nat.card h.K) h.H.index gammaDegree lambdaDegree
      hKeven hindexPos hcop hgammaDegreeNe hlambdaDegreeNe
      hdegreeInt hmainInt
  exact brauerSuzukiWall_index_cases_of_degree_equations
    (Nat.card h.K) h.H.index gammaDegree lambdaDegree
    hk hindexPos hdegreeInt hindexProduct hmainInt

end

end CFSG.GorensteinWalter
