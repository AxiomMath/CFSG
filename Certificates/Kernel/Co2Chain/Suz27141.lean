module

public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOrderEightCheck
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.Suz27141

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.Solomon78 CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.Suz2306

@[expose] noncomputable def X : Nat :=
  wordK 1782 11 (mask 11) (pidn 1782 11) triS triSI suzWordO8

@[expose] noncomputable def X2 : Nat := pcomp 1782 11 (mask 11) X X

@[expose] noncomputable def X4 : Nat := pcomp 1782 11 (mask 11) X2 X2

@[expose] noncomputable def X8 : Nat := pcomp 1782 11 (mask 11) X4 X4

theorem kWord : wordEqK 1782 11 (mask 11) (pidn 1782 11) triS triSI 3 suzWordO8 X = true := by
  quickRfl

theorem kSq : bAnd(compEqK 1782 11 (mask 11) (1782 * 11) X X X2,
    bAnd(compEqK 1782 11 (mask 11) (1782 * 11) X2 X2 X4,
      compEqK 1782 11 (mask 11) (1782 * 11) X4 X4 X8)) = true := by
  quickRfl

theorem kId : idK 1782 11 (mask 11) = true := by
  quickRfl

theorem kOrd : bAnd(eqK X8 (pidn 1782 11), neK 1782 11 (mask 11) (1782 * 11) X4 (pidn 1782 11)) =
    true := by
  quickRfl

theorem x_eq : suzArrO8 = unpack 1782 11 X := by
  have hS : bTriple.size = 3 ∧ ∀ j < 3, bTriple[j]! = unpack 1782 11 (triS j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · change bTriple[0]! = unpack 1782 11 B0
      simpa [bTriple] using b0Arr_eq
    · change bTriple[1]! = unpack 1782 11 B1
      simpa [bTriple] using b1Arr_eq
    · change bTriple[2]! = unpack 1782 11 V
      simpa [bTriple] using vArr_eq
  have h := (wordEqK_sound hS tri_perms kWord).1
  unfold suzArrO8 suzArr
  exact h

theorem check : suzOrderEightCheck = true := by
  obtain ⟨s2, s4, s8⟩ := (by simpa only [bAnd_iff] using kSq :
    compEqK 1782 11 (mask 11) (1782 * 11) X X X2 = true ∧
    compEqK 1782 11 (mask 11) (1782 * 11) X2 X2 X4 = true ∧
    compEqK 1782 11 (mask 11) (1782 * 11) X4 X4 X8 = true)
  obtain ⟨e8, n4⟩ := (by simpa only [bAnd_iff] using kOrd :
    eqK X8 (pidn 1782 11) = true ∧ neK 1782 11 (mask 11) (1782 * 11) X4 (pidn 1782 11) = true)
  have hid := idK_sound kId
  have hl : lettersOK 2 suzWordO8 = true := by decide
  unfold suzOrderEightCheck
  rw [x_eq, compEqK_sound s2, compEqK_sound s4, compEqK_sound s8, ← hid, eqK_sound e8,
    neK_sound n4, hl]
  rfl

end CertificateChecks.KernelCo2Chain.Suz27141

end
