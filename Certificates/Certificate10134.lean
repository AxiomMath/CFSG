module

public import Certificates.Data.SuzReal
import Certificates.Kernel.SuzPump.PairFacts
import Certificates.Kernel.Sporadic.Suz.Text2306
import CFSG.Certificates.Kernel.Misc.ArrEnumSound
import CFSG.Certificates.Kernel.Misc.ArrEnumOps
import CFSG.Certificates.Kernel.B3S3KSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.ArrBind

set_option maxRecDepth 400000

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.BfsPin CFSG.KS.PEnum
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore

namespace CertificateChecks.Batch10134

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.BfsPin CFSG.KS.PEnum
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore

noncomputable def SB (j : Nat) : Nat := cond (Nat.beq j 0) Suz2306.B0 Suz2306.B1

noncomputable def WK (w : List Nat) : Nat := wordTabK 1782 11 (mask 11) (pidn 1782 11) SB w

theorem kB : (permB 1782 11 Suz2306.B0 && permB 1782 11 Suz2306.B1) = true := by quickRfl

theorem letter_eq (hB0 : permB 1782 11 Suz2306.B0 = true) (hB1 : permB 1782 11 Suz2306.B1 = true)
    (l : Nat) : (if l = 0 then b0Arr else b1Arr) = unpack 1782 11 (SB l) ∧
      permB 1782 11 (SB l) = true := by
  unfold SB
  by_cases h : l = 0
  · subst h
    exact ⟨Suz2306.b0Arr_eq, hB0⟩
  · have hb : Nat.beq l 0 = false := by
      cases e : Nat.beq l 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [if_neg h, hb]
    exact ⟨Suz2306.b1Arr_eq, hB1⟩

theorem word_eq (hB0 : permB 1782 11 Suz2306.B0 = true) (hB1 : permB 1782 11 Suz2306.B1 = true) :
    ∀ w : List Nat, suzWordArr w = unpack 1782 11 (WK w) ∧ permB 1782 11 (WK w) = true
  | [] => ⟨idA_eq hw, permB_id hw⟩
  | l :: rest => by
    obtain ⟨ih1, ih2⟩ := word_eq hB0 hB1 rest
    obtain ⟨hS1, hS2⟩ := letter_eq hB0 hB1 l
    have e : WK (l :: rest) = pcomp 1782 11 (mask 11) (SB l) (WK rest) := by
      change strictN (WK rest) (fun acc => pcomp 1782 11 (mask 11) (SB l) acc) = _
      rw [strictN_app']
    have e2 : suzWordArr (l :: rest) =
        compA 1782 (if l = 0 then b0Arr else b1Arr) (suzWordArr rest) := rfl
    rw [e2, e, ih1, hS1, comp_unpack hw hS2 ih2]
    exact ⟨rfl, permB_pcomp hw hS2 ih2⟩

theorem inverts_of {w : List Nat} {X : Nat} {x : Array Nat} (ex : x = unpack 1782 11 X)
    (pX : permB 1782 11 X = true)
    (h : (w.all (fun l => decide (l < 2)) &&
      Nat.beq (pcomp 1782 11 (mask 11) (WK w) X)
        (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) X X) (WK w))) = true) :
    invertsOK w x = true := by
  have hb := kB
  simp only [Bool.and_eq_true] at hb
  obtain ⟨e1, p1⟩ := word_eq hb.1 hb.2 w
  have pXX := permB_pcomp hw pX pX
  unfold invertsOK
  dsimp only
  rw [e1, ex, comp_unpack hw p1 pX, comp_unpack hw pX pX, comp_unpack hw pXX p1,
    eqA_unpack hw (permB_pcomp hw p1 pX) (permB_pcomp hw pXX p1)]
  exact h

theorem atA : invertsOK suzRealWA (xAArr (levels ())) = true := by
  have rb : (reb xATuple).2.2 = true := by quickRfl
  exact inverts_of (rebuild_eq rb) (by quickRfl) (by quickRfl)

theorem atB : invertsOK suzRealWB (xBArr (levels ())) = true := by
  have rb : (reb xBTuple).2.2 = true := by quickRfl
  exact inverts_of (rebuild_eq rb) (by quickRfl) (by quickRfl)

theorem atY : invertsOK suzRealWY (yArr (levels ())) = true := by
  have rb : (reb yTuple).2.2 = true := by quickRfl
  exact inverts_of (rebuild_eq rb) (by quickRfl) (by quickRfl)

end CertificateChecks.Batch10134

public section

namespace Certificates

open CertificateChecks

theorem certificate10134 : CFSG.HardMathSupport.Dickson.I271.TabSuzFuse.suzRealOK () = true := by
  unfold suzRealOK
  dsimp only
  rw [CertificateChecks.Batch10134.atA, CertificateChecks.Batch10134.atB, CertificateChecks.Batch10134.atY]
  rfl

end Certificates
