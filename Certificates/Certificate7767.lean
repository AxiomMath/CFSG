module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.U52.Bind
import Certificates.Kernel.U52.ChainX
import Certificates.Kernel.U52.ChainSub
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
import CFSG.ClassicalGroups
import CFSG.GH74.Statements
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Milestones.ASVolI.F48.Rest.Eng
import CFSG.Milestones.ASVolI.F48.Rest.Perm
import CFSG.Milestones.ASVolI.F48.Small.Base
import CFSG.Milestones.ASVolI.F4Native
import CFSG.Permutation.BurnsideSchur
import CFSG.Quasithin.Background.F6Basic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Recognition.CertTwoLocalPair
import CFSG.Quasithin.Recognition.CertU33Wreath
import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
import CFSG.Sporadic.Schreier.J4SSylow
import Certificates.Kernel.J4Count.FixCE

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7767

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum
  CertificateChecks.KernelU52

private theorem bX : ∀ j < 6, arrBind (burnsideF48t_u52Gens ())[j]! 462 9 (CX.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

private theorem bP1 : ∀ j < 3, arrBind burnsideF48t_u52P1Arr[j]! 462 9 (CP1.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

private theorem bP2 : ∀ j < 3, arrBind burnsideF48t_u52P2Arr[j]! 462 9 (CP2.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

private theorem bB : ∀ j < 2, arrBind burnsideF48t_u52BArr[j]! 462 9 (CB.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

private theorem bS0 : allN 4 (fun j => Nat.beq
    (evFK 462 9 (mask 9) (pidn 462 9) LP LPI (burnsideF48t_u52SW.getD j [])) (CS0.S j)) = true := by
  quickRfl

private theorem bK : allN 2 (fun j => Nat.beq (evFK 462 9 (mask 9) (pidn 462 9) LP LPI
    (burnsideF48t_u52KW.getD (burnsideF48t_u52KGenIdx.getD j 0) [])) (CK.S j)) = true := by
  quickRfl

private theorem oS0 : (burnsideF48t_u52S0Arr ()).size = 4 ∧
    ∀ j < 4, (burnsideF48t_u52S0Arr ())[j]! = unpack 462 9 (CS0.S j) := by
  have hl : burnsideF48t_u52SW.length = 4 := by decide +kernel
  refine ⟨by simp [burnsideF48t_u52S0Arr, hl], fun j hj => ?_⟩
  rw [burnsideF48t_u52S0Arr, getD_map_toArray _ _ [] (by omega), ev_eq, Nat.eq_of_beq_eq_true (allN_spec bS0 j hj)]

private theorem oK : (burnsideF48t_u52KArr ()).size = 2 ∧
    ∀ j < 2, (burnsideF48t_u52KArr ())[j]! = unpack 462 9 (CK.S j) := by
  have hl : burnsideF48t_u52KGenIdx.length = 2 := by decide +kernel
  refine ⟨by simp [burnsideF48t_u52KArr, hl], fun j hj => ?_⟩
  rw [burnsideF48t_u52KArr, getD_map_toArray _ _ 0 (by omega), ev_eq, Nat.eq_of_beq_eq_true (allN_spec bK j hj)]

private theorem chainX : burnsideF48t_u52ChainXOK () = true := by
  rw [burnsideF48t_u52ChainXOK]
  exact chainCheck_of (CH := 16) (D := u52DX)
    ⟨by decide +kernel, fun j hj => arrBind_sound (bX j hj)⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num) ⟨by decide +kernel, by decide +kernel⟩
    CX.head CX.hl (by decide +kernel) CX.hs (by quickRfl) (by decide +kernel)

private theorem chainP1 : burnsideF48t_u52ChainP1OK () = true := by
  rw [burnsideF48t_u52ChainP1OK]
  exact chainCheck_of (CH := 16) (D := u52DP1)
    ⟨by decide +kernel, fun j hj => arrBind_sound (bP1 j hj)⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num) ⟨by decide +kernel, by decide +kernel⟩
    CP1.head CP1.hl (by decide +kernel) CP1.hs (by quickRfl) (by decide +kernel)

private theorem chainP2 : burnsideF48t_u52ChainP2OK () = true := by
  rw [burnsideF48t_u52ChainP2OK]
  exact chainCheck_of (CH := 16) (D := u52DP2)
    ⟨by decide +kernel, fun j hj => arrBind_sound (bP2 j hj)⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num) ⟨by decide +kernel, by decide +kernel⟩
    CP2.head CP2.hl (by decide +kernel) CP2.hs (by quickRfl) (by decide +kernel)

private theorem chainB : burnsideF48t_u52ChainBOK () = true := by
  rw [burnsideF48t_u52ChainBOK]
  exact chainCheck_of (CH := 16) (D := u52DB)
    ⟨by decide +kernel, fun j hj => arrBind_sound (bB j hj)⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num) ⟨by decide +kernel, by decide +kernel⟩
    CB.head CB.hl (by decide +kernel) CB.hs (by quickRfl) (by decide +kernel)

private theorem chainS0 : burnsideF48t_u52ChainS0OK () = true := by
  rw [burnsideF48t_u52ChainS0OK]
  exact chainCheck_of (CH := 16) (D := u52DS0) oS0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num) ⟨by decide +kernel, by decide +kernel⟩
    CS0.head CS0.hl (by decide +kernel) CS0.hs (by quickRfl) (by decide +kernel)

private theorem chainK : burnsideF48t_u52ChainKOK () = true := by
  rw [burnsideF48t_u52ChainKOK]
  exact chainCheck_of (CH := 16) (D := u52DK) oK (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num) ⟨by decide +kernel, by decide +kernel⟩
    CK.head CK.hl (by decide +kernel) CK.hs (by quickRfl) (by decide +kernel)

end CertificateChecks.Batch7767

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7767 : burnsideF48t_u52ChainXOK () = true ∧
    burnsideF48t_u52ChainP1OK () = true ∧
    burnsideF48t_u52ChainP2OK () = true ∧
    burnsideF48t_u52ChainBOK () = true ∧
    burnsideF48t_u52ChainS0OK () = true ∧
    burnsideF48t_u52ChainKOK () = true :=
  ⟨CertificateChecks.Batch7767.chainX, CertificateChecks.Batch7767.chainP1, CertificateChecks.Batch7767.chainP2, CertificateChecks.Batch7767.chainB, CertificateChecks.Batch7767.chainS0,
    CertificateChecks.Batch7767.chainK⟩

end Certificates

end
