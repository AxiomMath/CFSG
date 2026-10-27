module

public import CFSG.Quasithin.Recognition.M12AscS6b
public import Certificates.Certificate8083
import CFSG.Assembly.LowTwoRankDefs

public section

open Equiv CFSG.Quasithin

namespace CertificateChecks.Batch8950

open Equiv CFSG.Quasithin

private theorem ρ_pcp_0 : pcp = swap 3 4 * pa * swap 3 4 := by
  decide +kernel

private theorem z_ne_a_0 : ¬swap 0 1 = pa := by
  decide +kernel

private theorem exists_y0_0 : pcp * pa = pa * pcp := by
  decide +kernel

private theorem exists_y0_1 : pcp * pcp = 1 := by
  decide +kernel

private theorem exists_y0_2 : swap 0 1 * pcp = pcp * swap 0 1 := by
  decide +kernel

private theorem exists_y0_3 : pcp * swap 4 5 * pcp = swap 2 3 := by
  decide +kernel

end CertificateChecks.Batch8950

namespace Certificates

open CertificateChecks

open Equiv CFSG.Quasithin in
theorem certificate8950 : pcp = swap 3 4 * pa * swap 3 4 ∧ ¬swap 0 1 = pa ∧ pcp * pa = pa * pcp ∧
    pcp * pcp = 1 ∧ swap 0 1 * pcp = pcp * swap 0 1 ∧ pcp * swap 4 5 * pcp = swap 2 3 := by
  exact ⟨CertificateChecks.Batch8950.ρ_pcp_0, CertificateChecks.Batch8950.z_ne_a_0, CertificateChecks.Batch8950.exists_y0_0, CertificateChecks.Batch8950.exists_y0_1,
    CertificateChecks.Batch8950.exists_y0_2, CertificateChecks.Batch8950.exists_y0_3⟩

end Certificates
