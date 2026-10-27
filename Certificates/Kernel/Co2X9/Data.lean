module

public import Certificates.Kernel.Co2Syl.Small
public import Certificates.Data.Kernel.Co2X9
import CFSG.Certificates.Kernel.Common.F2Bfs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co2X9
  "Certificates/Kernel/Co2X9/data/small.json.gz" 1803 6674033210331174366
  (GLX : List Nat) (NX : Nat) (XW : Array (List Nat)) (DW : List Nat) (FW : List Nat)
  (EW : List Nat) (DX : Nat) (FX : Nat) (EX : Nat) (YX : Nat)

#kc_f2bfs CertificateChecks.KernelSpor.Co2X9.EN 22 CertificateChecks.KernelSpor.Co2X9.GLX 6144 6 19

#kc_repo #kc_ktree_gz CertificateChecks.KernelSpor.Co2X9 WX
  "Certificates/Kernel/Co2X9/data/wit.bin.gz" 24 4 2304 9265706331211511152

namespace CertificateChecks.KernelSpor.Co2X9

open CertificateChecks.KernelSpor.Co2Syl

@[expose] noncomputable def GX (j : Nat) : Nat := lAt GLX j

@[expose] noncomputable def WK (k : Nat) : Nat :=
  fld(WX (Nat.shiftRight k (nat_lit 6)), Nat.mul (Nat.land k (nat_lit 63)) (nat_lit 3), nat_lit 7)

end CertificateChecks.KernelSpor.Co2X9

end
