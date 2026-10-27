module

public import Certificates.Data.Kernel.Cert690.Pgl
public import Certificates.Kernel.Cert690.PglData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.Pgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

set_option maxHeartbeats 0 in
theorem f1 : pglF1K K.toArray (invsL K).toArray K0.toArray (invsL K0).toArray = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem f2 : (kPGLGens.all fun g => isoQ false g) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f4 : pglF4K K.toArray K0.toArray (invsL K).toArray (fun g => lookD K (invsL K) g 0)
    (commWitL K).toArray = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem f5 : pglF5K f5WitK = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f6 : pglF6K = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f7 : pglF7K K.toArray K0.toArray = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f8 : pglF8K K0.toArray = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f9 : pglF9K K.toArray (w9K K) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f12 : pglF12K K.toArray K0.toArray (invsL K).toArray (involL K).toArray
    (outersL K K0).toArray (w12L K K0).toArray = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem fOut : pglOutersK K.toArray K0.toArray (outersL K K0).toArray = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem f13 : pglF13K K.toArray K0.toArray = true := by decide +kernel

end CertificateChecks.KernelC690.Pgl

end
