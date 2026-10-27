module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LowNormVirtualCharacterDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Character decomposition in the Brauer--Suzuki--Wall argument

The transferred characters of norms three and two have exactly one signed
irreducible constituent in common.  Its two signs are opposite, yielding
Bender's decompositions `alpha = 1 + gamma - lambda` and
`beta = phi - gamma`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The low-norm and cross-pairing relations force Bender's three-term
signed irreducible decomposition. -/
public theorem brauerSuzukiWall_character_decomposition
    {G : Type u} [Group G] [Finite G]
    {alpha beta : Section1.ClassFunction G}
    (halphaVirtual : Theory.Character.IsVirtualCharacter alpha)
    (hbetaVirtual : Theory.Character.IsVirtualCharacter beta)
    (halphaNorm : Section1.scalarProduct G alpha alpha = 3)
    (hbetaNorm : Section1.scalarProduct G beta beta = 2)
    (halphaBeta : Section1.scalarProduct G alpha beta = -1)
    (halphaPrincipal :
      Section1.scalarProduct G alpha (Section1.principalCharacter G) = 1)
    (hbetaPrincipal :
      Section1.scalarProduct G beta (Section1.principalCharacter G) = 0) :
    ∃ gamma lambda phi : Section1.ClassFunction G,
      Section3.IsSignedIrreducibleCharacter gamma ∧
      Section3.IsSignedIrreducibleCharacter lambda ∧
      Section3.IsSignedIrreducibleCharacter phi ∧
      Section1.scalarProduct G gamma (Section1.principalCharacter G) = 0 ∧
      Section1.scalarProduct G lambda (Section1.principalCharacter G) = 0 ∧
      Section1.scalarProduct G phi (Section1.principalCharacter G) = 0 ∧
      Section1.scalarProduct G gamma lambda = 0 ∧
      Section1.scalarProduct G gamma phi = 0 ∧
      Section1.scalarProduct G lambda phi = 0 ∧
      alpha = Section1.principalCharacter G + gamma - lambda ∧
      beta = phi - gamma := by
  classical
  let principal : Section1.ClassFunction G := Section1.principalCharacter G
  have hprincipalIrr :
      Section1.IsIrreducibleCharacterOnGroup principal := by
    exact Section3.principalCharacter_isIrreducibleCharacterOnGroup
  have hprincipalSelf : Section1.scalarProduct G principal principal = 1 :=
    Section1.scalarProduct_irreducibleCharacter_self hprincipalIrr
  have hprincipalBeta : Section1.scalarProduct G principal beta = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) principal beta
    rw [hbetaPrincipal] at hswap
    simpa using hswap.symm
  have hbetaPlusVirtual :
      Theory.Character.IsVirtualCharacter (principal + beta) :=
    Section3.isVirtualCharacter_add
      Section3.isVirtualCharacter_principalCharacter hbetaVirtual
  have hbetaPlusPrincipal :
      Section1.scalarProduct G (principal + beta) principal = 1 := by
    rw [Section1.scalarProduct_add_left, hprincipalSelf, hbetaPrincipal]
    norm_num
  have hbetaPlusNorm :
      Section1.scalarProduct G (principal + beta) (principal + beta) = 3 := by
    rw [Section1.scalarProduct_add_left,
      Section5.scalarProduct_add_right, Section5.scalarProduct_add_right,
      hprincipalSelf, hprincipalBeta, hbetaPrincipal, hbetaNorm]
    norm_num
  obtain ⟨chiA, epsilonA, hchiAIrr, hchiAInj, hchiANonprincipal,
      hepsilonA, halphaDecomp⟩ :=
    low_norm_virtual_character_decomposition alpha 2 (Or.inl rfl)
      halphaVirtual halphaPrincipal (by
        convert halphaNorm using 1
        norm_num)
  obtain ⟨chiB, epsilonB, hchiBIrr, hchiBInj, hchiBNonprincipal,
      hepsilonB, hbetaPlusDecomp⟩ :=
    low_norm_virtual_character_decomposition (principal + beta) 2
      (Or.inl rfl) hbetaPlusVirtual hbetaPlusPrincipal
      (by
        convert hbetaPlusNorm using 1
        norm_num)
  have hweightedTwo
      (epsilon : Fin 2 → ℂ)
      (chi : Fin 2 → Section1.ClassFunction G) :
      Section1.weightedFamilySum epsilon chi =
        epsilon 0 • chi 0 + epsilon 1 • chi 1 := by
    ext g
    unfold Section1.weightedFamilySum
    rw [show @Finset.univ (Fin 2) (Fintype.ofFinite (Fin 2)) =
      @Finset.univ (Fin 2) (Fin.fintype 2) by ext; simp]
    rw [Fin.sum_univ_two]
    rfl
  let a : Fin 2 → Section1.ClassFunction G :=
    fun i => epsilonA i • chiA i
  let b : Fin 2 → Section1.ClassFunction G :=
    fun i => epsilonB i • chiB i
  have halphaEq : alpha = principal + (a 0 + a 1) := by
    rw [halphaDecomp, hweightedTwo]
  have hbetaEq : beta = b 0 + b 1 := by
    have hcancel := add_left_cancel hbetaPlusDecomp
    rw [hweightedTwo] at hcancel
    exact hcancel
  have haSigned : ∀ i, Section3.IsSignedIrreducibleCharacter (a i) := by
    intro i
    exact ⟨epsilonA i, hepsilonA i, chiA i, hchiAIrr i, rfl⟩
  have hbSigned : ∀ i, Section3.IsSignedIrreducibleCharacter (b i) := by
    intro i
    exact ⟨epsilonB i, hepsilonB i, chiB i, hchiBIrr i, rfl⟩
  have hpair (i j : Fin 2) :
      Section1.scalarProduct G (a i) (b j) =
        if chiA i = chiB j then epsilonA i * epsilonB j else 0 := by
    dsimp [a, b]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    by_cases hij : chiA i = chiB j
    · rw [if_pos hij, hij,
        Section1.scalarProduct_irreducibleCharacter_self (hchiBIrr j)]
      rcases hepsilonA i with hi | hi <;>
        rcases hepsilonB j with hj | hj <;> simp [hi, hj]
    · rw [if_neg hij,
        Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hchiAIrr i) (hchiBIrr j) hij]
      simp
  have hcross :
      Section1.scalarProduct G (a 0) (b 0) +
        Section1.scalarProduct G (a 0) (b 1) +
        Section1.scalarProduct G (a 1) (b 0) +
        Section1.scalarProduct G (a 1) (b 1) = -1 := by
    rw [halphaEq,
      Section1.scalarProduct_add_left,
      hprincipalBeta,
      Section1.scalarProduct_add_left,
      zero_add,
      hbetaEq,
      Section5.scalarProduct_add_right,
      Section5.scalarProduct_add_right] at halphaBeta
    simpa [add_assoc] using halphaBeta
  let other : Fin 2 → Fin 2 := fun i => ⟨1 - i.1, by omega⟩
  have hother_zero : other 0 = 1 := rfl
  have hother_one : other 1 = 0 := rfl
  have hmatch : ∃ i j : Fin 2,
      chiA i = chiB j ∧
      Section1.scalarProduct G (a i) (b j) = -1 ∧
      chiA (other i) ≠ chiB (other j) := by
    by_cases h00 : chiA 0 = chiB 0
    · have h01 : chiA 0 ≠ chiB 1 := by
        intro h
        have hz : (0 : Fin 2) = 1 :=
          hchiBInj (h00.symm.trans h)
        omega
      have h10 : chiA 1 ≠ chiB 0 := by
        intro h
        have hz : (1 : Fin 2) = 0 :=
          hchiAInj (h.trans h00.symm)
        omega
      by_cases h11 : chiA 1 = chiB 1
      · have hc := hcross
        rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
        rw [if_pos h00, if_neg h01, if_neg h10, if_pos h11] at hc
        rcases hepsilonA 0 with ha0 | ha0 <;>
          rcases hepsilonA 1 with ha1 | ha1 <;>
          rcases hepsilonB 0 with hb0 | hb0 <;>
          rcases hepsilonB 1 with hb1 | hb1 <;>
          norm_num [ha0, ha1, hb0, hb1] at hc
      · have hsp : Section1.scalarProduct G (a 0) (b 0) = -1 := by
          rw [hpair 0 0, if_pos h00]
          have hc := hcross
          rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
          rw [if_pos h00, if_neg h01, if_neg h10, if_neg h11] at hc
          simpa using hc
        exact ⟨0, 0, h00, hsp, by simpa [hother_zero] using h11⟩
    · by_cases h01 : chiA 0 = chiB 1
      · have h11 : chiA 1 ≠ chiB 1 := by
          intro h
          have hz : (1 : Fin 2) = 0 :=
            hchiAInj (h.trans h01.symm)
          omega
        by_cases h10 : chiA 1 = chiB 0
        · have hc := hcross
          rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
          rw [if_neg h00, if_pos h01, if_pos h10, if_neg h11] at hc
          rcases hepsilonA 0 with ha0 | ha0 <;>
            rcases hepsilonA 1 with ha1 | ha1 <;>
            rcases hepsilonB 0 with hb0 | hb0 <;>
            rcases hepsilonB 1 with hb1 | hb1 <;>
            norm_num [ha0, ha1, hb0, hb1] at hc
        · have hsp : Section1.scalarProduct G (a 0) (b 1) = -1 := by
            rw [hpair 0 1, if_pos h01]
            have hc := hcross
            rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
            rw [if_neg h00, if_pos h01, if_neg h10, if_neg h11] at hc
            simpa using hc
          exact ⟨0, 1, h01, hsp, by
            simpa [hother_zero, hother_one] using h10⟩
      · by_cases h10 : chiA 1 = chiB 0
        · have h11 : chiA 1 ≠ chiB 1 := by
            intro h
            have hz : (0 : Fin 2) = 1 :=
              hchiBInj (h10.symm.trans h)
            omega
          have hsp : Section1.scalarProduct G (a 1) (b 0) = -1 := by
            rw [hpair 1 0, if_pos h10]
            have hc := hcross
            rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
            rw [if_neg h00, if_neg h01, if_pos h10, if_neg h11] at hc
            simpa using hc
          exact ⟨1, 0, h10, hsp, by
            simpa [hother_zero, hother_one] using h01⟩
        · have h11 : chiA 1 = chiB 1 := by
            by_contra h11
            have hc := hcross
            rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
            rw [if_neg h00, if_neg h01, if_neg h10, if_neg h11] at hc
            norm_num at hc
          have hsp : Section1.scalarProduct G (a 1) (b 1) = -1 := by
            rw [hpair 1 1, if_pos h11]
            have hc := hcross
            rw [hpair 0 0, hpair 0 1, hpair 1 0, hpair 1 1] at hc
            rw [if_neg h00, if_neg h01, if_neg h10, if_pos h11] at hc
            simpa using hc
          exact ⟨1, 1, h11, hsp, by
            simpa [hother_one] using h00⟩
  obtain ⟨i, j, hij, hsharedPair, hotherNe⟩ := hmatch
  have hshared : b j = -a i := by
    dsimp [a, b] at hsharedPair ⊢
    rw [← hij] at hsharedPair ⊢
    rw [Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right,
      Section1.scalarProduct_irreducibleCharacter_self (hchiAIrr i)]
      at hsharedPair
    rcases hepsilonA i with ha | ha
    · rcases hepsilonB j with hb | hb
      · exfalso
        norm_num [ha, hb] at hsharedPair
      · simp [ha, hb]
    · rcases hepsilonB j with hb | hb
      · simp [ha, hb]
      · exfalso
        norm_num [ha, hb] at hsharedPair
  have hsumA : a i + a (other i) = a 0 + a 1 := by
    fin_cases i <;> simp [hother_zero, hother_one, add_comm]
  have hsumB : b j + b (other j) = b 0 + b 1 := by
    fin_cases j <;> simp [hother_zero, hother_one, add_comm]
  let gamma : Section1.ClassFunction G := a i
  let lambda : Section1.ClassFunction G :=
    (-epsilonA (other i)) • chiA (other i)
  let phi : Section1.ClassFunction G := b (other j)
  have hlambdaEq : lambda = -a (other i) := by
    ext g
    simp [lambda, a]
  have hnegativeSign : Section1.IsSign (-epsilonA (other i)) := by
    rcases hepsilonA (other i) with h | h <;>
      simp [Section1.IsSign, h]
  have hgammaSigned : Section3.IsSignedIrreducibleCharacter gamma :=
    haSigned i
  have hlambdaSigned : Section3.IsSignedIrreducibleCharacter lambda :=
    ⟨-epsilonA (other i), hnegativeSign, chiA (other i),
      hchiAIrr (other i), rfl⟩
  have hphiSigned : Section3.IsSignedIrreducibleCharacter phi :=
    hbSigned (other j)
  have horthogonal_smul
      {epsilon delta : ℂ}
      {chi psi : Section1.ClassFunction G}
      (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
      (hpsi : Section1.IsIrreducibleCharacterOnGroup psi)
      (hne : chi ≠ psi) :
      Section1.scalarProduct G (epsilon • chi) (delta • psi) = 0 := by
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hchi hpsi hne]
    simp
  have hprincipal_smul
      {epsilon : ℂ} {chi : Section1.ClassFunction G}
      (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
      (hne : chi ≠ principal) :
      Section1.scalarProduct G (epsilon • chi) principal = 0 := by
    rw [Section1.scalarProduct_smul_left,
      Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        hchi hprincipalIrr hne]
    simp
  have hiOther : chiA i ≠ chiA (other i) := by
    intro heq
    have hiEq := hchiAInj heq
    fin_cases i <;> simp [hother_zero, hother_one] at hiEq
  have hjOther : chiB j ≠ chiB (other j) := by
    intro heq
    have hjEq := hchiBInj heq
    fin_cases j <;> simp [hother_zero, hother_one] at hjEq
  have hgammaPrincipal : Section1.scalarProduct G gamma principal = 0 := by
    exact hprincipal_smul (hchiAIrr i) (hchiANonprincipal i)
  have hlambdaPrincipal : Section1.scalarProduct G lambda principal = 0 := by
    exact hprincipal_smul (hchiAIrr (other i))
      (hchiANonprincipal (other i))
  have hphiPrincipal : Section1.scalarProduct G phi principal = 0 := by
    exact hprincipal_smul (hchiBIrr (other j))
      (hchiBNonprincipal (other j))
  have hgammaLambda : Section1.scalarProduct G gamma lambda = 0 := by
    exact horthogonal_smul (hchiAIrr i) (hchiAIrr (other i)) hiOther
  have hgammaPhi : Section1.scalarProduct G gamma phi = 0 := by
    exact horthogonal_smul (hchiAIrr i) (hchiBIrr (other j)) (by
      intro heq
      exact hjOther (hij.symm.trans heq))
  have hlambdaPhi : Section1.scalarProduct G lambda phi = 0 := by
    exact horthogonal_smul (hchiAIrr (other i))
      (hchiBIrr (other j)) hotherNe
  have halphaFinal : alpha = principal + gamma - lambda := by
    rw [halphaEq, ← hsumA]
    simp [gamma, hlambdaEq, sub_eq_add_neg, add_assoc]
  have hbetaFinal : beta = phi - gamma := by
    rw [hbetaEq, ← hsumB, hshared]
    simp [phi, gamma, sub_eq_add_neg, add_comm]
  exact ⟨gamma, lambda, phi, hgammaSigned, hlambdaSigned, hphiSigned,
    hgammaPrincipal, hlambdaPrincipal, hphiPrincipal,
    hgammaLambda, hgammaPhi, hlambdaPhi, halphaFinal, hbetaFinal⟩

end CFSG.GorensteinWalter
