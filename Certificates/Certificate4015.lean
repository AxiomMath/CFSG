module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZfGens
import Certificates.Kernel.J4Q.ZFrGens
public import Certificates.Data.Kernel.J4Q.ZFr

public section

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.A5

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 in
theorem certificate4015 : ZfGens := by
  have h := KernelJ4Q.zfGensOK_true
  unfold zfGensOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨h.1, fun g hg => h.2 g hg⟩

end Certificates
