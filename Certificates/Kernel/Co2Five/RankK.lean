module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2FiveRankInputs
meta import CFSG.RankThree.Native.Co2FiveData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo2Five.Co2FiveTxt CFSG.RankThree.Native.co2FiveHex
#kmisc_hexflat CertificateChecks.KernelCo2Five.Co2FiveTxt CFSG.RankThree.Native.co2FiveHex 3 2300 12 2

namespace CertificateChecks.KernelCo2Five

open CFSG.KC.Enum CFSG.KS.Co2M CertificateChecks.KernelSporSch.Co2M
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

@[expose] noncomputable def lineK (r i : Nat) : Nat := pg 12 4095 (Co2FiveTxt.F r) i

@[expose] noncomputable def lineDiffK (r i : Nat) : Nat := VG (PV 0) (lineK r i) ^^^ VG (PV 0) i

@[expose] noncomputable def rankOfK (r : Nat) (idx dual : List Nat) : Bool :=
  idx.all (· < 2300) && dual.length == idx.length &&
    (List.range idx.length).all fun k => (List.range idx.length).all fun l =>
      dot22 (dual.getD k 0) (lineDiffK r (idx.getD l 0)) == (k == l)

theorem rank_k : (allN 2300 (fun i => decide (lineK 0 i < 2300) && decide (lineK 1 i < 2300)) &&
    rankOfK 0 co2RankIdx0 co2RankDual0 && rankOfK 1 co2RankIdx1 co2RankDual1) = true := by
  decide +kernel

theorem rank_neg : (!rankOfK 1 co2RankIdx0 co2RankDual0) = true := by decide +kernel

end CertificateChecks.KernelCo2Five

end
