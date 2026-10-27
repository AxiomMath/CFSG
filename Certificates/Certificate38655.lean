module

public import CFSG.GF2Type.SmithTypeE.LMod.Basic
import Certificates.Kernel.SmithL6K.GlueQ

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod in
open CFSG.LargeExtraspecial.SMod20 (V) in
theorem certificate38655 : ∀ v : V, (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 :=
  KernelSmithL6K.cv_zero

end Certificates
