module

import Certificates.Kernel.Fi22F.Agree
public import Certificates.Certificate9110
import Certificates.Kernel.Fi22F.Three

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.Fi22Exact in
open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration in
theorem certificate9108 : ([0, 0] ∈ codes W0)
    ∧ (List.replicate 13 2 ∈ codes W0)
    ∧ ((List.replicate 11 [0, 2]).flatten ∈ codes W0)
    ∧ ((List.replicate 21 [0, 2, 2]).flatten ∈ codes W0)
    ∧ (wsF.all (fun w => w.length % 2 == 0) = true)
    ∧ (g1w.length = 11011)
    ∧ (g2w.length = 2520) :=
  ⟨KernelFi22F.rel_a2_mem, KernelFi22F.rel_b13_mem, KernelFi22F.rel_ab11_mem,
    KernelFi22F.rel_ab2_21_mem, KernelFi22F.even_rels, KernelFi22F.len_g1, KernelFi22F.len_g2⟩

end Certificates
