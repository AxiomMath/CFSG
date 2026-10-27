module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCharacterRelations
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallTISubset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedCharacterVirtual
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1ScalarProductCompatibility
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_9

namespace CFSG
end CFSG
open CFSG

/-!
# Transferred characters in the Brauer--Suzuki--Wall argument

Suzuki's relative-TI induction theorem transfers Bender's two generalized
characters from `H` to `G`, preserving their values on nonidentity elements
of `K`, their pairings, and their pairings with the principal character.
-/

namespace CFSG.GorensteinWalter

noncomputable section

universe u

open BenderGlauberman
open BenderSuzuki.External
open Theory.Character

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

/-- Bender's two generalized characters retain all of their character
relations after relative-TI induction from `H` to `G`. -/
public theorem BrauerSuzukiWallHypotheses.transferred_character_relations
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {rho sigma : ClassFunction h.K}
    (hrho : IsLinearCharacter rho)
    (hsigma : IsLinearCharacter sigma)
    (hrhoNot : ¬ ∀ x : h.K, rho x⁻¹ = rho x)
    (hsigmaNot : ¬ ∀ x : h.K, sigma x⁻¹ = sigma x)
    (hrhoT : rho ⟨h.t, h.t_mem_K⟩ = 1)
    (hsigmaT : sigma ⟨h.t, h.t_mem_K⟩ = -1) :
    let hKleH : h.K ≤ h.H := by
      rw [h.H_eq_join]
      exact le_sup_left
    let alpha : ClassFunction h.H :=
      inducedFromSub hKleH ((1 : ClassFunction h.K) - rho)
    let beta : ClassFunction h.H :=
      inducedFromSub hKleH (rho - sigma)
    let alphaStar : ClassFunction G := Section1.inducedCF h.H alpha
    let betaStar : ClassFunction G := Section1.inducedCF h.H beta
    IsVirtualCharacter alphaStar ∧
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
          (Section1.principalCharacter G) = 0 := by
  classical
  let hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  let alpha : ClassFunction h.H :=
    inducedFromSub hKleH ((1 : ClassFunction h.K) - rho)
  let beta : ClassFunction h.H :=
    inducedFromSub hKleH (rho - sigma)
  let alphaStar : ClassFunction G := Section1.inducedCF h.H alpha
  let betaStar : ClassFunction G := Section1.inducedCF h.H beta
  have hrels :=
    h.character_relations hrho hsigma hrhoNot hsigmaNot hrhoT hsigmaT
  change IsGeneralizedCharacter alpha ∧
      IsGeneralizedCharacter beta ∧
      alpha 1 = 0 ∧ beta 1 = 0 ∧
      alpha ⟨h.t, hKleH h.t_mem_K⟩ = 0 ∧
      beta ⟨h.t, hKleH h.t_mem_K⟩ = 4 ∧
      normSq h.H alpha = 3 ∧ normSq h.H beta = 2 ∧
      scalarProduct h.H alpha beta = -1 ∧
      ∀ x : h.H, (x : G) ∉ h.K → alpha x = 0 ∧ beta x = 0 at hrels
  rcases hrels with
    ⟨halphaGen, hbetaGen, halphaOne, hbetaOne, halphaT, hbetaT,
      halphaNorm, hbetaNorm, halphaBeta, hsupport⟩
  have halphaVirtual : IsVirtualCharacter alpha :=
    generalizedCharacter_isVirtualCharacter halphaGen
  have hbetaVirtual : IsVirtualCharacter beta :=
    generalizedCharacter_isVirtualCharacter hbetaGen
  have halphaSupport : ∀ x : h.H, (x : G) ∉ h.K → alpha x = 0 :=
    fun x hx => (hsupport x hx).1
  have hbetaSupport : ∀ x : h.H, (x : G) ∉ h.K → beta x = 0 :=
    fun x hx => (hsupport x hx).2
  have halphaStarVirtual : IsVirtualCharacter alphaStar := by
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      h.H halphaVirtual
  have hbetaStarVirtual : IsVirtualCharacter betaStar := by
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      h.H hbetaVirtual
  have hpropAlpha := Suzuki.VI.suzuki_ch6_proposition_2_9
    h.H (h.K : Set G) h.isTISubsetRelative alpha
      halphaVirtual halphaSupport
  have hpropBeta := Suzuki.VI.suzuki_ch6_proposition_2_9
    h.H (h.K : Set G) h.isTISubsetRelative beta
      hbetaVirtual hbetaSupport
  have hvalues : ∀ (x : G) (hx : x ∈ h.K), x ≠ 1 →
      alphaStar x = alpha ⟨x, hKleH hx⟩ ∧
        betaStar x = beta ⟨x, hKleH hx⟩ := by
    intro x hx hxne
    constructor
    · simpa [alphaStar] using hpropAlpha.1 x hx hxne
    · simpa [betaStar] using hpropBeta.1 x hx hxne
  have halphaStarOne : alphaStar 1 = 0 := by
    have hdeg := Section1.degree_inducedClassFunction h.H alpha
    change alphaStar 1 = (h.H.index : ℂ) * alpha 1 at hdeg
    rw [halphaOne, mul_zero] at hdeg
    exact hdeg
  have hbetaStarOne : betaStar 1 = 0 := by
    have hdeg := Section1.degree_inducedClassFunction h.H beta
    change betaStar 1 = (h.H.index : ℂ) * beta 1 at hdeg
    rw [hbetaOne, mul_zero] at hdeg
    exact hdeg
  have halphaStarT : alphaStar h.t = 0 := by
    have hv := hpropAlpha.1 h.t h.t_mem_K h.t_involution.1
    change alphaStar h.t =
      alpha ⟨h.t, h.isTISubsetRelative.1 h.t_mem_K⟩ at hv
    simpa using hv.trans (by simpa using halphaT)
  have hbetaStarT : betaStar h.t = 4 := by
    have hv := hpropBeta.1 h.t h.t_mem_K h.t_involution.1
    change betaStar h.t =
      beta ⟨h.t, h.isTISubsetRelative.1 h.t_mem_K⟩ at hv
    simpa using hv.trans (by simpa using hbetaT)
  have halphaStarNorm :
      Section1.scalarProduct G alphaStar alphaStar = 3 := by
    have hv := hpropAlpha.2.2 halphaOne alpha halphaVirtual halphaSupport
    change Section1.scalarProduct G alphaStar alphaStar =
      Section1.scalarProduct h.H alpha alpha at hv
    exact hv.trans ((section1_scalarProduct_eq_theory alpha alpha).trans (by
      simpa [normSq] using halphaNorm))
  have hbetaStarNorm :
      Section1.scalarProduct G betaStar betaStar = 2 := by
    have hv := hpropBeta.2.2 hbetaOne beta hbetaVirtual hbetaSupport
    change Section1.scalarProduct G betaStar betaStar =
      Section1.scalarProduct h.H beta beta at hv
    exact hv.trans ((section1_scalarProduct_eq_theory beta beta).trans (by
      simpa [normSq] using hbetaNorm))
  have halphaStarBeta :
      Section1.scalarProduct G alphaStar betaStar = -1 := by
    have hv := hpropAlpha.2.2 halphaOne beta hbetaVirtual hbetaSupport
    change Section1.scalarProduct G alphaStar betaStar =
      Section1.scalarProduct h.H alpha beta at hv
    exact hv.trans
      ((section1_scalarProduct_eq_theory alpha beta).trans halphaBeta)
  have hrhoNeOne : rho ≠ (1 : ClassFunction h.K) := by
    intro heq
    apply hrhoNot
    intro x
    rw [heq]
    rfl
  have hsigmaNeOne : sigma ≠ (1 : ClassFunction h.K) := by
    intro heq
    apply hsigmaNot
    intro x
    rw [heq]
    rfl
  have honeIrr : IsIrreducibleCharacter (1 : ClassFunction h.K) :=
    (isLinearCharacter_one (G := h.K)).1
  have honeClass : IsClassFunction (1 : ClassFunction h.H) := by
    intro _ _
    rfl
  have halphaPrincipalH :
      Section1.scalarProduct h.H alpha
          (Section1.principalCharacter h.H) = 1 := by
    rw [section1_scalarProduct_eq_theory]
    change scalarProduct h.H alpha (1 : ClassFunction h.H) = 1
    change scalarProduct h.H
      (inducedFromSub hKleH ((1 : ClassFunction h.K) - rho))
      (1 : ClassFunction h.H) = 1
    rw [frobenius_reciprocity_inducedFromSub hKleH
      ((1 : ClassFunction h.K) - rho) honeClass]
    change scalarProduct h.K ((1 : ClassFunction h.K) - rho)
      (1 : ClassFunction h.K) = 1
    rw [scalarProduct_sub_left,
      scalarProduct_irr_ite honeIrr honeIrr,
      scalarProduct_irr_ite hrho.1 honeIrr]
    simp [hrhoNeOne]
  have hbetaPrincipalH :
      Section1.scalarProduct h.H beta
          (Section1.principalCharacter h.H) = 0 := by
    rw [section1_scalarProduct_eq_theory]
    change scalarProduct h.H beta (1 : ClassFunction h.H) = 0
    change scalarProduct h.H
      (inducedFromSub hKleH (rho - sigma))
      (1 : ClassFunction h.H) = 0
    rw [frobenius_reciprocity_inducedFromSub hKleH
      (rho - sigma) honeClass]
    change scalarProduct h.K (rho - sigma)
      (1 : ClassFunction h.K) = 0
    rw [scalarProduct_sub_left,
      scalarProduct_irr_ite hrho.1 honeIrr,
      scalarProduct_irr_ite hsigma.1 honeIrr]
    simp [hrhoNeOne, hsigmaNeOne]
  have halphaStarPrincipal :
      Section1.scalarProduct G alphaStar
          (Section1.principalCharacter G) = 1 := by
    change Section1.scalarProduct G (Section1.inducedCF h.H alpha)
      (Section1.principalCharacter G) = 1
    exact hpropAlpha.2.1.trans halphaPrincipalH
  have hbetaStarPrincipal :
      Section1.scalarProduct G betaStar
          (Section1.principalCharacter G) = 0 := by
    change Section1.scalarProduct G (Section1.inducedCF h.H beta)
      (Section1.principalCharacter G) = 0
    exact hpropBeta.2.1.trans hbetaPrincipalH
  exact ⟨halphaStarVirtual, hbetaStarVirtual, hvalues,
    halphaStarOne, hbetaStarOne, halphaStarT, hbetaStarT,
    halphaStarNorm, hbetaStarNorm, halphaStarBeta,
    halphaStarPrincipal, hbetaStarPrincipal⟩

end

end CFSG.GorensteinWalter
