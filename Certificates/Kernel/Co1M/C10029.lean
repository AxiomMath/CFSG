module

public import CFSG.Monster.GMS.CoTwoMain
public import CFSG.Monster.GMS.CoTwoModule
public import CFSG.Monster.GMS.CoTwoPerfectGen
public import CFSG.Sporadic.Co1.Module.CoTwoNortonData
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1M.Data10029
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.Facts.Section36
public import CFSG.Monster.GMS.NotConj
public import CFSG.Sporadic.Co1.Module.CoTwoData
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Kernel.Co1B.Tri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KD.Co1M CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.Module.CoTwo CertificateChecks.KernelCo1Cover

@[expose] def cmRPA : List Nat := R0 :: R1 :: RPAT

theorem cm_progA_chk : progK 24 cmRPA PROGAL 2 = true := by quickRfl

theorem cm_progAL : PROGAL = progA := eq_of_beq (by quickRfl)

theorem cm_regsA : regsRowsA = (cmRPA.map (unpackR 24)).toArray := by
  rw [regsRowsA, initRowsA, rowsA_eq, rowsB_eq, ← cm_progAL, ← prog_sound cm_progA_chk]
  rfl

theorem cm_getLA (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L.getD i x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => cm_getLA x L i

theorem cm_rrA {i : Nat} (hi : i < cmRPA.length) : rrA i = unpackR 24 (getL 0 cmRPA i) := by
  rw [rrA, cm_regsA, cm_getLA, List.getD_eq_getElem _ _ hi]
  simp [hi]

theorem cm_lenA : cmRPA.length = 24 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c10029_r1 : rrA 13 = r1Rows := by
  rw [cm_rrA (by rw [cm_lenA]; omega)]
  decide +kernel

theorem c10029_r2 : rrA 18 = r2Rows := by
  rw [cm_rrA (by rw [cm_lenA]; omega)]
  decide +kernel

open Certificates in
open CFSG.Sporadic.Co1.Module.CoTwo in
theorem c10029 :
    (rrA 13 = r1Rows)
    ∧ (rrA 18 = r2Rows) := ⟨c10029_r1, c10029_r2⟩

end CertificateChecks.KernelCo1M

end
