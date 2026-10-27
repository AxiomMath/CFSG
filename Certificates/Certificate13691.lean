module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8
import Certificates.Kernel.Direct.C13691O
import Certificates.Kernel.Direct.C13691S0
import Certificates.Kernel.Direct.C13691S1
import Certificates.Kernel.Direct.C13691S2
import Certificates.Kernel.Direct.C13691S3
import Certificates.Kernel.Direct.C13691S4

public section

open CFSG.HardMathSupport.Timmesfeld.Steinberg

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelDirect.C13691 in
theorem certificate13691 : CFSG.HardMathSupport.Timmesfeld.Steinberg.e8ThreeCheck () = true := by
  unfold e8ThreeCheck
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨e8ThreeOrbit_ok, ?_⟩
  intro S hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  exacts [e8ThreeStab0_ok, e8ThreeStab1_ok, e8ThreeStab2_ok, e8ThreeStab3_ok, e8ThreeStab4_ok]

end Certificates
