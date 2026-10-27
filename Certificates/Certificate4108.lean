module

import Certificates.Kernel.J4Q.D4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Native
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Wit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B0

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
open CFSG.Sporadic.J4 in
theorem certificate4108 : ((Dec2.chkGrp b1344Words && Dec2.chkGrp a85Words &&
            chkD4 d4Reps d4Words d4Wit [b1344Words, a85Words]) = true) := by
  simp only [Bool.and_eq_true]
  exact ⟨⟨KernelJ4Q.d4_grp_b, KernelJ4Q.d4_grp_a⟩, KernelJ4Q.d4_all⟩

end Certificates
