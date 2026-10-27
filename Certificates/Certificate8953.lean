module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Certificate3120
public import Certificates.Certificate3172

public section

open Matrix

namespace CertificateChecks.Batch8953

open Matrix

private theorem adj_transvection_two_0 {i j : Fin 3} (hij : i ≠ j) :
    (adjugate (Matrix.transvection i j (1 : ZMod 2)))ᵀ = Matrix.transvection j i 1 := by
  rw [adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel

end CertificateChecks.Batch8953

namespace Certificates

open CertificateChecks

open Matrix in
theorem certificate8953 : ∀ {i j : Fin 3}, i ≠ j →
    (adjugate (Matrix.transvection i j (1 : ZMod 2)))ᵀ = Matrix.transvection j i 1 := by
  exact CertificateChecks.Batch8953.adj_transvection_two_0

end Certificates
