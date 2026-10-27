module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Co2Smith.GlNJInputs
public meta import CFSG.Sporadic.Co2Smith.GlNJInputs
public import CFSG.Certificates.InvariantMerge
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

@[expose] def chJcD : List (List Int) := glNJChW.toList.drop 2

meta def chJcB : Array Nat := glNJChBase.toArray

end CertificateChecks.KernelCo2Smith

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelCo2Smith.CJc 77 7 8 128
  CFSG.Sporadic.Co2Smith.Native.glNJChS CertificateChecks.KernelCo2Smith.chJcB 2
  CertificateChecks.KernelCo2Smith.chJcD

#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 0 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 1 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 2 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 3 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 4 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 5 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelCo2Smith.CJc 6 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 0 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 1 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 2 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 3 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 4 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 5 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelCo2Smith.CJc 6 0 10
#ks_rawchain_sl2_join CertificateChecks.KernelCo2Smith.CJc

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Smith.Native

theorem jcBind_k : (glNJChS.size == 8 && allN 8 (fun k => bindListK 77 7 (CJc.S k) (glNJChS[k]!).toList) &&
    bindListK 77 7 (CJc.S 0) (glNJPerm[0]!).toList && bindListK 77 7 (CJc.S 1) (glNJPerm[1]!).toList &&
    glNJChW.size == 8) = true := by
  decide +kernel

theorem jc_neg : (!bindListK 77 7 (CJc.S 0) (glNJPerm[1]!).toList) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
