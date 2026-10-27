module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFIIPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaMinusDPHigh
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3POmegaMinusSDHigh
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeLowPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeLowPOmegaMinusTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFIIPSL

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckM3POmegaMinusDualPairHigh_holds :
    RCKM3POmegaMinusDualPairHigh := by
  intro n f hf hn S hSU hS hodd ε e hε he heε hne hdeg J' hJe
  exact rckM3_POmegaMinus_dualPairHigh n f hf hn S hSU hS hodd hε he heε hne hdeg hJe

theorem rckM3POmegaMinusSelfDualHigh_holds :
    RCKM3POmegaMinusSelfDualHigh := by
  intro n f hf hn S hSU hS hodd e hε he hdeg J' hJe
  exact rckM3_POmegaMinus_selfDualHigh n f hf hn S hSU hS hodd hε he hdeg hJe

@[expose] def RCKLemmaFAtPOmegaMinusThree :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    (∃ (g : ℕ) (φ : (ggU .POmegaMinus 3 g).K →* X), 1 ≤ g ∧ φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .POmegaMinus 3 g).K ∧
      ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus 3 g).D φ b) →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → GGRootPosFlag K R

@[expose] def RCKLemmaFIIAtPOmegaMinusThree :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    (∃ (g : ℕ) (φ : (ggU .POmegaMinus 3 g).K →* X), 1 ≤ g ∧ φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .POmegaMinus 3 g).K ∧
      ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus 3 g).D φ b) →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → GGSixRCKJRow .II J →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → Nat.card R = 2 → GGRootPosNbr K R

theorem rckLemmaFAtPOmegaMinusLow_of
    (hIRG : RCKIntrinsicRoot) (h3 : RCKLemmaFAtPOmegaMinusThree) :
    RCKLemmaFAtPOmegaMinusLow := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hA6 hRJ hRmJ hroot
  obtain ⟨m, g, φ, hm, hg, hφr, hφk, hdiag⟩ := hmodel
  have hcases : m ≤ 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hcases with hm1 | rfl | rfl
  · exact (rckPOmegaMinus_false_of_le_one hm1 φ hφr hcomp).elim
  · exact rckLemmaFAt_PSL hIRG X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
      (rckClassicalModelIDAt_PSL_of_omegaMinus_two hg hBK φ hφr hφk hdiag) hodd hcomp hA6 hRJ
      hRmJ hroot
  · exact h3 X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank ⟨g, φ, hg, hφr, hφk, hdiag⟩ hodd
      hcomp hA6 hRJ hRmJ hroot

theorem rckLemmaFIIAtPOmegaMinusLow_of
    (hIRG : RCKIntrinsicRoot) (h3 : RCKLemmaFIIAtPOmegaMinusThree) :
    RCKLemmaFIIAtPOmegaMinusLow := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hrow hA6 hRJ hRmJ hroot
    hR2
  obtain ⟨m, g, φ, hm, hg, hφr, hφk, hdiag⟩ := hmodel
  have hcases : m ≤ 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hcases with hm1 | rfl | rfl
  · exact (rckPOmegaMinus_false_of_le_one hm1 φ hφr hcomp).elim
  · exact rckLemmaFIIAt_PSL hIRG X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
      (rckClassicalModelIDAt_PSL_of_omegaMinus_two hg hBK φ hφr hφk hdiag) hodd hcomp hrow hA6 hRJ
      hRmJ hroot hR2
  · exact h3 X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank ⟨g, φ, hg, hφr, hφk, hdiag⟩ hodd
      hcomp hrow hA6 hRJ hRmJ hroot hR2

theorem rckLemmaFAt_POmegaMinus_of_three
    (hIRG : RCKIntrinsicRoot) (h3 : RCKLemmaFAtPOmegaMinusThree) : RCKLemmaFAt .POmegaMinus :=
  rckLemmaFAt_POmegaMinus_of hIRG rckM3POmegaMinusDualPairHigh_holds
    rckM3POmegaMinusSelfDualHigh_holds (rckLemmaFAtPOmegaMinusLow_of hIRG h3)

theorem rckLemmaFIIAt_POmegaMinus_of_three
    (hIRG : RCKIntrinsicRoot) (h3 : RCKLemmaFIIAtPOmegaMinusThree) :
    RCKLemmaFIIAt .POmegaMinus :=
  rckLemmaFIIAt_POmegaMinus_of hIRG rckM3POmegaMinusDualPairHigh_holds
    rckM3POmegaMinusSelfDualHigh_holds (rckLemmaFIIAtPOmegaMinusLow_of hIRG h3)

end CFSG.StandardType.RCKRP
