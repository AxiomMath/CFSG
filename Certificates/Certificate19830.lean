module

public import Certificates.Data.HSFiveTables
public import CFSG.RankThree.Native.HSMcLSmallData
import Certificates.Kernel.Misc.Perm.HS100.BaseGlue

public section

namespace Certificates

open CertificateChecks.KernelMisc.HS100 CFSG.KS.Raw

private theorem hsTabA_eq : unpack 100 7 (HX.F 0) = Certificates.MaxD2Heis.hsTabA := by
  decide +kernel

private theorem hsTabB_eq : unpack 100 7 (HX.F 1) = Certificates.MaxD2Heis.hsTabB := by
  decide +kernel

private theorem hsTabU_eq : unpack 100 7 (HX.F 15) = Certificates.MaxD2Heis.hsTabU := by
  decide +kernel

theorem certificate19830 : CFSG.RankThree.Native.hs100Arr 0 = Certificates.MaxD2Heis.hsTabA ∧
    CFSG.RankThree.Native.hs100Arr 1 = Certificates.MaxD2Heis.hsTabB ∧
    CFSG.RankThree.Native.hs100Arr 15 = Certificates.MaxD2Heis.hsTabU ∧
    Certificates.MaxD2Heis.hsTabA.size = 100 ∧ Certificates.MaxD2Heis.hsTabB.size = 100 ∧
    Certificates.MaxD2Heis.hsTabU.size = 100 :=
  ⟨by rw [hs100Arr_eq 0 (by norm_num), hsTabA_eq], by rw [hs100Arr_eq 1 (by norm_num), hsTabB_eq],
    by rw [hs100Arr_eq 15 (by norm_num), hsTabU_eq], by decide +kernel, by decide +kernel,
    by decide +kernel⟩

end Certificates
