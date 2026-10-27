module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagOmPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagOmMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestOrder
public import CFSG.LocalAnalysis.StandardType.SUCenterOdd
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSpinCenter
public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSpinCenterTwo
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal

theorem rckFlag_oddCenter_SL (m g : ℕ) (hg : 1 ≤ g) :
    OddCenterOf (Matrix.SpecialLinearGroup.toGL (n := Fin (m + 1)) (R := GaloisField 2 g)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.StandardType.SLRest.odd_card_center_SL (K := GaloisField 2 g) (d := m + 1)

theorem rckFlag_oddCenter_SU (n g : ℕ) (hg : 1 ≤ g) :
    OddCenterOf (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.StandardType.odd_natCard_of_le_center_SU
    (F := GaloisField 2 (2 * g))
    (σ := CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) (n := n)
    (H := Subgroup.center (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n)) le_rfl

theorem rckFlag_oddCenter_Sp (n g : ℕ) (hg : 1 ≤ g) :
    OddCenterOf (CFSG.Open.StatedSp n (GaloisField 2 g)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold OddCenterOf
  rw [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := GaloisField 2 g) n,
    Subgroup.card_bot]
  exact odd_one

@[expose] def RCKFlagSpinPlusFourOdd : Prop :=
  ∀ g : ℕ, 1 ≤ g → OddCenterOf (Spin.spinMatrix (Spin.quadPlus 2 (GaloisField 2 g)))

theorem rckFlag_oddCenter_quadMinus_two
    (g : ℕ) (hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadMinus 2 (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus 2 (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) :=
    (MonoidHom.ker_eq_bot_iff _).1 (Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 g) h2)
  haveI : Finite (spinGroup (Spin.quadMinus 2 (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := Finite.of_injective _ hinj
  exact CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_of_centerPPrime_two
    (CFSG.StandardType.RCKC1.rckGL4_centerPPrime_spinMinus_two (minusCoeffs_irr 2 g))

theorem rckFlag_oddCenter_OmPlus (hS : RCKFlagSpinPlusFourOdd) (n g : ℕ) (hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 g))) := by
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    · exact rckFlagSC_oddCenter_quadPlus_zero g hg
    · exact rckFlagSC2_oddCenter_quadPlus_one g hg
    · exact hS g hg
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    unfold OddCenterOf
    rw [CFSG.SeitzReduction.OmegaPilot.center_spinGroup_quadPlus_eq_bot'
      (F := GaloisField 2 g) (n := n) hn, Subgroup.card_bot]
    exact odd_one

theorem rckFlag_oddCenter_OmMinus
    (n g : ℕ) (hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) := by
  rcases lt_or_ge n 4 with hn | hn
  · interval_cases n
    · exact rckFlagSC2_oddCenter_quadMinus_zero g hg
    · exact rckFlagSC2_oddCenter_quadMinus_one g hg
    · exact rckFlag_oddCenter_quadMinus_two g hg
    · exact rckFlagSC_oddCenter_quadMinus_three g hg
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    unfold OddCenterOf
    rw [CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot
      (F := GaloisField 2 g) (n := n) hn (minusCoeffs_irr 2 g), Subgroup.card_bot]
    exact odd_one

theorem rckK2FlagRootSub_of_spinPlusFour
    (hS : RCKFlagSpinPlusFourOdd) : RCKK2FlagRootSub := by
  intro X _ _ K R hpos r hr hr1
  rcases hpos with ⟨m, g, hg, h⟩ | ⟨n, g, hg, h⟩ | ⟨n, g, hg, h⟩ | ⟨n, g, hg, h⟩ | ⟨n, g, hg, h⟩
  · exact flagAt_pCoreOf_le _ _ (rckFlag_oddCenter_SL m g hg) (rckFlagCent_SL m g hg) h r hr hr1
  · exact flagAt_pCoreOf_le _ _ (rckFlag_oddCenter_SU n g hg) (rckFlagCent_SU n g hg) h r hr hr1
  · exact flagAt_pCoreOf_le _ _ (rckFlag_oddCenter_Sp n g hg) (rckFlagCent_Sp n g hg) h r hr hr1
  · exact flagAt_pCoreOf_le _ _ (rckFlag_oddCenter_OmPlus hS n g hg)
      (rckFlagCent_OmPlus n g hg) h r hr hr1
  · exact flagAt_pCoreOf_le _ _ (rckFlag_oddCenter_OmMinus n g hg)
      (rckFlagCent_OmMinus n g hg) h r hr hr1

end CFSG.StandardType.RCKFlag
