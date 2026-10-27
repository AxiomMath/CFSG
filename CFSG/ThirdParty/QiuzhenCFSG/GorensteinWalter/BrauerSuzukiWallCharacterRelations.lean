module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallInducedCharacters

namespace CFSG
end CFSG
open CFSG

/-!
# The initial Brauer--Suzuki--Wall generalized characters

This is the calculation in `refs/bender-bsw.tex`, lines 112--119.  From the
two selected linear characters of `K`, it forms Bender's generalized
characters `alpha` and `beta` on `H` and proves their values, norms, mutual
scalar product, and support.
-/

namespace CFSG.GorensteinWalter

noncomputable section

universe u

open BenderGlauberman
open Theory.Character

attribute [local instance] Classical.propDecidable

/-- Bender's initial generalized-character calculation for the
Brauer--Suzuki--Wall order argument. -/
public theorem BrauerSuzukiWallHypotheses.character_relations
    {G : Type u} [Group G] [Fintype G]
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
    let beta : ClassFunction h.H := inducedFromSub hKleH (rho - sigma)
    IsGeneralizedCharacter alpha ∧
      IsGeneralizedCharacter beta ∧
      alpha 1 = 0 ∧ beta 1 = 0 ∧
      alpha ⟨h.t, hKleH h.t_mem_K⟩ = 0 ∧
      beta ⟨h.t, hKleH h.t_mem_K⟩ = 4 ∧
      normSq h.H alpha = 3 ∧ normSq h.H beta = 2 ∧
      scalarProduct h.H alpha beta = -1 ∧
      ∀ x : h.H, (x : G) ∉ h.K → alpha x = 0 ∧ beta x = 0 := by
  classical
  let hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  let rhoH : ClassFunction h.H := inducedFromSub hKleH rho
  let sigmaH : ClassFunction h.H := inducedFromSub hKleH sigma
  have hsH : h.s ∈ h.H := by
    rw [h.H_eq_join]
    exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers h.s)
  have hsK : ∀ x : h.K, h.s * (x : G) * h.s⁻¹ ∈ h.K := by
    intro x
    rw [h.s_inverts_K (x : G) x.2]
    exact h.K.inv_mem x.2
  let rhoS : ClassFunction h.K := conjChar h.K hsK rho
  let sigmaS : ClassFunction h.K := conjChar h.K hsK sigma
  have hss : h.s * h.s = 1 := by
    simpa [pow_two] using h.s_involution.2
  have hsinv : h.s⁻¹ = h.s := inv_eq_of_mul_eq_one_right hss
  have hsKInv : ∀ x : h.K, h.s⁻¹ * (x : G) * h.s ∈ h.K := by
    intro x
    simpa [hsinv] using hsK x
  have hdouble (nu : ClassFunction h.K) :
      conjChar h.K hsK (conjChar h.K hsK nu) = nu := by
    ext x
    simp only [conjChar, conjMonoidHom]
    congr 1
    apply Subtype.ext
    have hunder : h.s * (h.s * (x : G) * h.s⁻¹) * h.s⁻¹ = (x : G) := by
      rw [hsinv]
      calc
        h.s * (h.s * (x : G) * h.s) * h.s =
            (h.s * h.s) * (x : G) * (h.s * h.s) := by group
        _ = x := by rw [hss]; simp
    exact hunder
  have honeFixed : conjChar h.K hsK (1 : ClassFunction h.K) = 1 := by
    ext x
    rfl
  have hrhoNeOne : rho ≠ (1 : ClassFunction h.K) := by
    intro heq
    apply hrhoNot
    intro x
    rw [heq]
    rfl
  have hrhoSNeOne : rhoS ≠ (1 : ClassFunction h.K) := by
    intro heq
    apply hrhoNeOne
    calc
      rho = conjChar h.K hsK rhoS := by
        simpa [rhoS] using (hdouble rho).symm
      _ = conjChar h.K hsK (1 : ClassFunction h.K) := by rw [heq]
      _ = 1 := honeFixed
  have hrhoSIrr : IsIrreducibleCharacter rhoS := by
    exact isIrreducibleCharacter_conjChar h.K hsK hsKInv hrho.1
  have hsigmaNeOne : sigma ≠ (1 : ClassFunction h.K) := by
    intro heq
    have hv := hsigmaT
    rw [heq] at hv
    norm_num at hv
  have hsigmaSNeOne : sigmaS ≠ (1 : ClassFunction h.K) := by
    intro heq
    apply hsigmaNeOne
    calc
      sigma = conjChar h.K hsK sigmaS := by
        simpa [sigmaS] using (hdouble sigma).symm
      _ = conjChar h.K hsK (1 : ClassFunction h.K) := by rw [heq]
      _ = 1 := honeFixed
  have hsigmaSIrr : IsIrreducibleCharacter sigmaS := by
    exact isIrreducibleCharacter_conjChar h.K hsK hsKInv hsigma.1
  have hresRho :
      (fun x : h.K => rhoH ⟨(x : G), hKleH x.2⟩) = rho + rhoS := by
    ext x
    have hv :=
      (remark_1_4 hKleH h.index_K_H hsH h.s_not_mem_K hrho.1).1
        (x : G) x.2 (hsK x)
    simpa [rhoH, rhoS, conjChar, conjMonoidHom] using hv
  have hpairOneRho :
      scalarProduct h.H (inducedFromSub hKleH (1 : ClassFunction h.K)) rhoH = 0 := by
    have hfrob := frobenius_reciprocity_inducedFromSub hKleH
      (1 : ClassFunction h.K)
      (isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter
        ((h.induced_linear_characters hrho hsigma hrhoNot hsigmaNot
          hrhoT hsigmaT).1)))
    change scalarProduct h.H
      (inducedFromSub hKleH (1 : ClassFunction h.K)) rhoH = 0
    rw [hfrob, hresRho, scalarProduct_add_right]
    rw [scalarProduct_irr_ite (isLinearCharacter_one (G := h.K)).1 hrho.1]
    rw [scalarProduct_irr_ite (isLinearCharacter_one (G := h.K)).1 hrhoSIrr]
    simp [hrhoNeOne.symm, hrhoSNeOne.symm]
  have hresSigma :
      (fun x : h.K => sigmaH ⟨(x : G), hKleH x.2⟩) = sigma + sigmaS := by
    ext x
    have hv :=
      (remark_1_4 hKleH h.index_K_H hsH h.s_not_mem_K hsigma.1).1
        (x : G) x.2 (hsK x)
    simpa [sigmaH, sigmaS, conjChar, conjMonoidHom] using hv
  have hind := h.induced_linear_characters
    hrho hsigma hrhoNot hsigmaNot hrhoT hsigmaT
  rcases hind with
    ⟨hrhoHIrr0, hsigmaHIrr0, hrhoSigmaNe0,
      hrhoOne0, hsigmaOne0, hrhoT0, hsigmaT0⟩
  have hrhoHIrr : IsIrreducibleCharacter rhoH := by
    simpa [rhoH, hKleH] using hrhoHIrr0
  have hsigmaHIrr : IsIrreducibleCharacter sigmaH := by
    simpa [sigmaH, hKleH] using hsigmaHIrr0
  have hrhoSigmaNe : rhoH ≠ sigmaH := by
    simpa [rhoH, sigmaH, hKleH] using hrhoSigmaNe0
  have hrhoOne : rhoH 1 = 2 := by
    simpa [rhoH, hKleH] using hrhoOne0
  have hsigmaOne : sigmaH 1 = 2 := by
    simpa [sigmaH, hKleH] using hsigmaOne0
  have hrhoT' : rhoH ⟨h.t, hKleH h.t_mem_K⟩ = 2 := by
    simpa [rhoH, hKleH] using hrhoT0
  have hsigmaT' : sigmaH ⟨h.t, hKleH h.t_mem_K⟩ = -2 := by
    simpa [sigmaH, hKleH] using hsigmaT0
  have hpairOneSigma :
      scalarProduct h.H (inducedFromSub hKleH (1 : ClassFunction h.K)) sigmaH = 0 := by
    have hfrob := frobenius_reciprocity_inducedFromSub hKleH
      (1 : ClassFunction h.K)
      (isCharacter_isClassFunction
        (isCharacter_of_isIrreducibleCharacter hsigmaHIrr))
    change scalarProduct h.H
      (inducedFromSub hKleH (1 : ClassFunction h.K)) sigmaH = 0
    rw [hfrob, hresSigma, scalarProduct_add_right]
    rw [scalarProduct_irr_ite (isLinearCharacter_one (G := h.K)).1 hsigma.1]
    rw [scalarProduct_irr_ite (isLinearCharacter_one (G := h.K)).1 hsigmaSIrr]
    simp [hsigmaNeOne.symm, hsigmaSNeOne.symm]
  let oneInd : ClassFunction h.H :=
    inducedFromSub hKleH (1 : ClassFunction h.K)
  have honeIndChar : IsCharacter oneInd := by
    exact isCharacter_ind_index_two h.K h.H hKleH h.index_K_H hsH
      h.s_not_mem_K (isLinearCharacter_one (G := h.K)).1 hsK
  have honeNormInv : scalarProductInv h.H oneInd oneInd = 2 := by
    exact scalarProductInv_ind_index_two_of_fixed h.K h.H hKleH h.index_K_H
      hsH h.s_not_mem_K (isLinearCharacter_one (G := h.K)).1 hsK honeFixed
  have honeNorm : normSq h.H oneInd = 2 := by
    have hb : star (scalarProduct h.H oneInd oneInd) =
        scalarProductInv h.H oneInd oneInd :=
      star_scalarProduct_eq_inv_of_char honeIndChar
    have hv : scalarProduct h.H oneInd oneInd = 2 := by
      apply star_inj.mp
      simpa using hb.trans honeNormInv
    exact hv
  have hpairRhoOne : scalarProduct h.H rhoH oneInd = 0 := by
    rw [← scalarProduct_conj]
    simp [oneInd, hpairOneRho]
  have hpairSigmaOne : scalarProduct h.H sigmaH oneInd = 0 := by
    rw [← scalarProduct_conj]
    simp [oneInd, hpairOneSigma]
  have hpairRhoSigma : scalarProduct h.H rhoH sigmaH = 0 := by
    rw [scalarProduct_irr_ite hrhoHIrr hsigmaHIrr]
    simp [hrhoSigmaNe]
  have hpairSigmaRho : scalarProduct h.H sigmaH rhoH = 0 := by
    rw [scalarProduct_irr_ite hsigmaHIrr hrhoHIrr]
    simp [hrhoSigmaNe.symm]
  have honeFormula (x : G) (hx : x ∈ h.K) :
      oneInd ⟨x, hKleH hx⟩ = 2 := by
    have hv :=
      (remark_1_4 hKleH h.index_K_H hsH h.s_not_mem_K
        (isLinearCharacter_one (G := h.K)).1).1 x hx (hsK ⟨x, hx⟩)
    norm_num at hv
    simpa [oneInd] using hv
  have honeOne : oneInd 1 = 2 := by
    have hv := honeFormula 1 h.K.one_mem
    have hHone : (⟨(1 : G), hKleH h.K.one_mem⟩ : h.H) = 1 := rfl
    rwa [hHone] at hv
  have honeT : oneInd ⟨h.t, hKleH h.t_mem_K⟩ = 2 :=
    honeFormula h.t h.t_mem_K
  have hIndSub (mu nu : ClassFunction h.K) :
      inducedFromSub hKleH (mu - nu) =
        inducedFromSub hKleH mu - inducedFromSub hKleH nu := by
    unfold inducedFromSub
    change inducedClassFunction (h.K.subgroupOf h.H)
      (fun x : ↥(h.K.subgroupOf h.H) =>
        mu ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩ -
          nu ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) =
      inducedClassFunction (h.K.subgroupOf h.H)
        (fun x : ↥(h.K.subgroupOf h.H) =>
          mu ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) -
      inducedClassFunction (h.K.subgroupOf h.H)
        (fun x : ↥(h.K.subgroupOf h.H) =>
          nu ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩)
    rw [← inducedClassFunction_sub]
    rfl
  let alpha : ClassFunction h.H :=
    inducedFromSub hKleH ((1 : ClassFunction h.K) - rho)
  let beta : ClassFunction h.H := inducedFromSub hKleH (rho - sigma)
  have halphaEq : alpha = oneInd - rhoH := by
    simpa [alpha, oneInd, rhoH] using
      hIndSub (1 : ClassFunction h.K) rho
  have hbetaEq : beta = rhoH - sigmaH := by
    simpa [beta, rhoH, sigmaH] using hIndSub rho sigma
  have hgenOfChar {phi : ClassFunction h.H} (hphi : IsCharacter phi) :
      IsGeneralizedCharacter phi := by
    exact ⟨phi, 0, hphi, isCharacter_zero, by simp⟩
  have halphaGen : IsGeneralizedCharacter alpha := by
    rw [halphaEq]
    exact isGeneralizedCharacter_sub_char (hgenOfChar honeIndChar)
      (isCharacter_of_isIrreducibleCharacter hrhoHIrr)
  have hbetaGen : IsGeneralizedCharacter beta := by
    rw [hbetaEq]
    exact isGeneralizedCharacter_sub_char
      (hgenOfChar (isCharacter_of_isIrreducibleCharacter hrhoHIrr))
      (isCharacter_of_isIrreducibleCharacter hsigmaHIrr)
  have halphaOne : alpha 1 = 0 := by
    rw [halphaEq]
    change oneInd 1 - rhoH 1 = 0
    rw [honeOne, hrhoOne]
    norm_num
  have hbetaOne : beta 1 = 0 := by
    rw [hbetaEq]
    change rhoH 1 - sigmaH 1 = 0
    rw [hrhoOne, hsigmaOne]
    norm_num
  have halphaT : alpha ⟨h.t, hKleH h.t_mem_K⟩ = 0 := by
    rw [halphaEq]
    change oneInd ⟨h.t, hKleH h.t_mem_K⟩ -
      rhoH ⟨h.t, hKleH h.t_mem_K⟩ = 0
    rw [honeT, hrhoT']
    norm_num
  have hbetaT : beta ⟨h.t, hKleH h.t_mem_K⟩ = 4 := by
    rw [hbetaEq]
    change rhoH ⟨h.t, hKleH h.t_mem_K⟩ -
      sigmaH ⟨h.t, hKleH h.t_mem_K⟩ = 4
    rw [hrhoT', hsigmaT']
    norm_num
  have halphaNorm : normSq h.H alpha = 3 := by
    rw [halphaEq]
    change scalarProduct h.H (oneInd - rhoH) (oneInd - rhoH) = 3
    rw [scalarProduct_sub_left, scalarProduct_sub_right,
      scalarProduct_sub_right]
    have honePair : scalarProduct h.H oneInd oneInd = 2 := honeNorm
    rw [honePair, hpairOneRho, hpairRhoOne,
      scalarProduct_irreducible_self hrhoHIrr]
    norm_num
  have hbetaNorm : normSq h.H beta = 2 := by
    rw [hbetaEq]
    change scalarProduct h.H (rhoH - sigmaH) (rhoH - sigmaH) = 2
    rw [scalarProduct_sub_left, scalarProduct_sub_right,
      scalarProduct_sub_right]
    rw [scalarProduct_irreducible_self hrhoHIrr, hpairRhoSigma,
      hpairSigmaRho, scalarProduct_irreducible_self hsigmaHIrr]
    norm_num
  have halphaBeta : scalarProduct h.H alpha beta = -1 := by
    rw [halphaEq, hbetaEq]
    rw [scalarProduct_sub_left, scalarProduct_sub_right,
      scalarProduct_sub_right]
    rw [hpairOneRho, hpairOneSigma,
      scalarProduct_irreducible_self hrhoHIrr, hpairRhoSigma]
    norm_num
  have hsupport : ∀ x : h.H, (x : G) ∉ h.K →
      alpha x = 0 ∧ beta x = 0 := by
    intro x hx
    constructor
    · exact inducedFromSub_eq_zero_of_not_mem h.K h.H hKleH h.index_K_H hx
    · exact inducedFromSub_eq_zero_of_not_mem h.K h.H hKleH h.index_K_H hx
  exact ⟨halphaGen, hbetaGen, halphaOne, hbetaOne, halphaT, hbetaT,
    halphaNorm, hbetaNorm, halphaBeta, hsupport⟩

end

end CFSG.GorensteinWalter
