module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallPairCountCharacterFormula
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallTransferredCharacters

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Pair-count pairings for the transferred characters

Frobenius reciprocity and the support of Bender's local generalized
characters determine their transferred scalar products with the
involution-pair count.
-/

namespace CFSG.GorensteinWalter

noncomputable section

universe u

open Theory.Character
open BenderGlauberman

attribute [local instance] Fintype.ofFinite

/-- The transferred generalized characters `alphaStar` and `betaStar` pair
with Bender's involution-pair count as `|K|` and `0`, respectively. -/
public theorem BrauerSuzukiWallHypotheses.pairCount_pairings
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
    Section1.scalarProduct G alphaStar (bswPairCountClassFunction G) =
        (Nat.card h.K : ℂ) ∧
      Section1.scalarProduct G betaStar (bswPairCountClassFunction G) = 0 := by
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
  have hlocal := h.character_relations
    hrho hsigma hrhoNot hsigmaNot hrhoT hsigmaT
  change IsGeneralizedCharacter alpha ∧
      IsGeneralizedCharacter beta ∧
      alpha 1 = 0 ∧ beta 1 = 0 ∧
      alpha ⟨h.t, hKleH h.t_mem_K⟩ = 0 ∧
      beta ⟨h.t, hKleH h.t_mem_K⟩ = 4 ∧
      normSq h.H alpha = 3 ∧ normSq h.H beta = 2 ∧
      scalarProduct h.H alpha beta = -1 ∧
      ∀ x : h.H, (x : G) ∉ h.K → alpha x = 0 ∧ beta x = 0 at hlocal
  rcases hlocal with
    ⟨_halphaGen, _hbetaGen, halphaOne, hbetaOne, _halphaT, _hbetaT,
      _halphaNorm, _hbetaNorm, _halphaBeta, hsupport⟩
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
    ⟨_halphaVirtual, _hbetaVirtual, _hvalues,
      _halphaStarOne, _hbetaStarOne, _halphaStarT, _hbetaStarT,
      _halphaStarNorm, _hbetaStarNorm, _halphaStarBeta,
      halphaStarPrincipal, hbetaStarPrincipal⟩
  have hpairClass := (h.pairCount_character_formula).1
  have halphaPrincipalH :
      Section1.scalarProduct h.H alpha (Section1.principalCharacter h.H) = 1 := by
    have hfrob := Section1.scalarProduct_inducedCF_left h.H alpha
      (Section1.principalCharacter G)
      (by intro x g; rfl)
    change Section1.scalarProduct G alphaStar
        (Section1.principalCharacter G) =
      Section1.scalarProduct h.H alpha
        (Section1.principalCharacter h.H) at hfrob
    rw [halphaStarPrincipal] at hfrob
    exact hfrob.symm
  have hbetaPrincipalH :
      Section1.scalarProduct h.H beta (Section1.principalCharacter h.H) = 0 := by
    have hfrob := Section1.scalarProduct_inducedCF_left h.H beta
      (Section1.principalCharacter G)
      (by intro x g; rfl)
    change Section1.scalarProduct G betaStar
        (Section1.principalCharacter G) =
      Section1.scalarProduct h.H beta
        (Section1.principalCharacter h.H) at hfrob
    rw [hbetaStarPrincipal] at hfrob
    exact hfrob.symm
  have hpairing (delta : ClassFunction h.H)
      (hdeltaOne : delta 1 = 0)
      (hdeltaSupport : ∀ x : h.H, (x : G) ∉ h.K → delta x = 0) :
      Section1.scalarProduct h.H delta
          (Section1.subgroupRestriction h.H (bswPairCountClassFunction G)) =
        (Nat.card h.K : ℂ) *
          Section1.scalarProduct h.H delta
            (Section1.principalCharacter h.H) := by
    let : Fintype h.H := Fintype.ofFinite h.H
    unfold Section1.scalarProduct
    calc
      (Nat.card h.H : ℂ)⁻¹ *
          ∑ x : h.H,
            delta x * star
              (Section1.subgroupRestriction h.H
                (bswPairCountClassFunction G) x) =
        (Nat.card h.H : ℂ)⁻¹ *
          ∑ x : h.H,
            (Nat.card h.K : ℂ) *
              (delta x * star (Section1.principalCharacter h.H x)) := by
        apply congrArg (fun z : ℂ => (Nat.card h.H : ℂ)⁻¹ * z)
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxOne : (x : G) = 1
        · have hx : x = 1 := Subtype.ext hxOne
          subst x
          simp [hdeltaOne, Section1.subgroupRestriction]
        · by_cases hxK : (x : G) ∈ h.K
          · have hcount := bswPairCount_eq_card_K h hxK hxOne
            simp [Section1.subgroupRestriction, bswPairCountClassFunction,
              hcount, Section1.principalCharacter_apply]
            ring
          · rw [hdeltaSupport x hxK]
            simp
      _ = (Nat.card h.H : ℂ)⁻¹ *
          ((Nat.card h.K : ℂ) *
            ∑ x : h.H,
              delta x * star (Section1.principalCharacter h.H x)) := by
        rw [← Finset.mul_sum]
      _ = (Nat.card h.K : ℂ) *
          ((Nat.card h.H : ℂ)⁻¹ *
            ∑ x : h.H,
              delta x * star (Section1.principalCharacter h.H x)) := by
        ring
  have halphaFrob := Section1.scalarProduct_inducedCF_left h.H alpha
    (bswPairCountClassFunction G) hpairClass
  have hbetaFrob := Section1.scalarProduct_inducedCF_left h.H beta
    (bswPairCountClassFunction G) hpairClass
  change Section1.scalarProduct G alphaStar (bswPairCountClassFunction G) =
      Section1.scalarProduct h.H alpha
        (Section1.subgroupRestriction h.H (bswPairCountClassFunction G))
    at halphaFrob
  change Section1.scalarProduct G betaStar (bswPairCountClassFunction G) =
      Section1.scalarProduct h.H beta
        (Section1.subgroupRestriction h.H (bswPairCountClassFunction G))
    at hbetaFrob
  change Section1.scalarProduct G alphaStar (bswPairCountClassFunction G) =
      (Nat.card h.K : ℂ) ∧
    Section1.scalarProduct G betaStar (bswPairCountClassFunction G) = 0
  constructor
  · calc
      Section1.scalarProduct G alphaStar (bswPairCountClassFunction G) =
          Section1.scalarProduct h.H alpha
            (Section1.subgroupRestriction h.H
              (bswPairCountClassFunction G)) := halphaFrob
      _ = (Nat.card h.K : ℂ) *
          Section1.scalarProduct h.H alpha
            (Section1.principalCharacter h.H) :=
        hpairing alpha halphaOne (fun x hx => (hsupport x hx).1)
      _ = Nat.card h.K := by rw [halphaPrincipalH]; simp
  · calc
      Section1.scalarProduct G betaStar (bswPairCountClassFunction G) =
          Section1.scalarProduct h.H beta
            (Section1.subgroupRestriction h.H
              (bswPairCountClassFunction G)) := hbetaFrob
      _ = (Nat.card h.K : ℂ) *
          Section1.scalarProduct h.H beta
            (Section1.principalCharacter h.H) :=
        hpairing beta hbetaOne (fun x hx => (hsupport x hx).2)
      _ = 0 := by rw [hbetaPrincipalH]; simp

end

end CFSG.GorensteinWalter
