module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
import Certificates.Kernel.UnitarySix.Hunt3003
import Certificates.Kernel.UnitarySix.M22Chunks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.ComponentClassification.WittDesign in
theorem certificate3003 : (rootCheck 256 tab8 list8 = true ∧ rootCheck 256 tab0 list0 = true ∧
      rootCheck 512 tabY listY = true ∧ list8.Pairwise (fun a b => keyT a < keyT b) ∧
      list0.Pairwise (fun a b => keyT a < keyT b) ∧ listY.Pairwise (fun a b => keyT a < keyT b))
    ∧ (m22Count (fun f => (missOut (tf tab8) list8 f || missOut (tf tab0) list0 f || missIn (tf
        tabY) listY f) = true) = 0)
    ∧ (m22Count (fun f => sqMulB (tf tab8) f = true) = 1716)
    ∧ (m22Count (fun f => (sqB f && !eqB id f) = true) = 1155)
    ∧ (m22Count (fun f => commB (tf tab8) f = true) = 1344)
    ∧ (m22Count (fun f => commB (tf tab0) f = true) = 320)
    ∧ (m22Count (fun f => commB (tf tabY) f = true) = 384) := KernelU6.cert3003

end Certificates
