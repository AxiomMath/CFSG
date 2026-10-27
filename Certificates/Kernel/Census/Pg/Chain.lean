module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
public import Certificates.Data.Kernel.W16Pg
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPg

@[expose] def dNil : List (List ℤ) := []

end CertificateChecks.KernelPg

end

#ks_rawchain CertificateChecks.KernelPg.C 128 8 16
  CFSG.EvenSporadicStandard.Fin76b.W16.sgsArr CFSG.EvenSporadicStandard.Fin76b.W16.baseArr 36
  CertificateChecks.KernelPg.dNil
#kmisc_packarrs CertificateChecks.KernelPg.ET CFSG.EvenSporadicStandard.Fin76b.W16.eTab 5

public section

namespace CertificateChecks.KernelPg

open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
  CFSG.KC.W16Pg

theorem bS : ∀ j < 36, arrBind sgsArr[j]! 128 8 (C.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bE : ∀ a < 32, arrBind eTab[a]! 32 5 (ET a) = true := by
  intro a ha
  interval_cases a <;> quickRfl

theorem perm : allN 36 (fun j => permOK 128 8 (mask 8) (128 * 8) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 6, baseArr[t]! = pg 8 (mask 8) C.BP t := by decide +kernel

theorem orbProd : ((List.range 6).map fun i => rcnt (C.LR i)).prod = 3317760 := by decide +kernel

theorem hNS : 128 ≤ C.NS * 16 := by decide +kernel

theorem aut_ok : autK ET C.S = true := by decide +kernel

theorem table_ok : tableG (mulCK ET) = true := by decide +kernel

theorem gen_ok : genG (mulCK ET) = true := by
  simp only [genG, ← Array.all_toList]
  decide +kernel

theorem cand_ok : candG (mulCK ET) = true := by decide +kernel

end CertificateChecks.KernelPg
