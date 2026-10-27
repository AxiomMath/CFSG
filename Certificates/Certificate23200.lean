module

public import Certificates.Data.TBLitL34PFieldCheck
import Certificates.Kernel.L34W.Field23200PChecks
import Certificates.Kernel.L34W.Glue
import CFSG.Certificates.Kernel.L34W.Field23200PSound

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.L34W

private theorem r2_eq23200 : CFSG.PSL3Four.Native.r₂T = CFSG.KS.Raw.unpack 42 6 (KernelL34W.GT 4) :=
  (KernelL34W.gensG 4 (by decide)).1

open CFSG.ComponentClassification.TBLit.L34P in
theorem certificate23200 : l34pFieldOK = true :=
  l34pFieldOK_of KernelL34W.t1Of KernelL34W.alOf KernelL34W.bounds_k KernelL34W.ch23200pa_k
    (fieldK_of_fieldP KernelL34W.gensG r2_eq23200 (KernelL34W.gensG 4 (by decide)).2
      KernelL34W.ch23200p_k)

end Certificates
