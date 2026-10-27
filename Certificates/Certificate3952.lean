module

public import CFSG.LieType.Chevalley.SignStabilizerDataE8Inputs

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CertificateChecks.Batch3952

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem e8SignOrbit_check_0 : OrbitCheck .E8 e8SignReps e8SignOrbit := by
  unfold OrbitCheck
  decide +kernel

private theorem e8SignStab0_check_1 : e8SignStab0.check e8Certificate = true := by
  decide +kernel

private theorem e8SignStab0_passing_2 : (e8SignStab0.passing e8Certificate).length ≤ 1 := by
  decide +kernel

private theorem e8SignStab1_check_3 : e8SignStab1.check e8Certificate = true := by
  decide +kernel

private theorem e8SignStab1_passing_4 : (e8SignStab1.passing e8Certificate).length ≤ 1 := by
  decide +kernel

private theorem e8SignStab2_check_5 : e8SignStab2.check e8Certificate = true := by
  decide +kernel

private theorem e8SignStab2_passing_6 : (e8SignStab2.passing e8Certificate).length ≤ 1 := by
  decide +kernel

end CertificateChecks.Batch3952

namespace Certificates

open CertificateChecks

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem certificate3952 : OrbitCheck .E8 e8SignReps e8SignOrbit
    ∧ e8SignStab0.check e8Certificate = true ∧ (e8SignStab0.passing e8Certificate).length ≤ 1
    ∧ e8SignStab1.check e8Certificate = true ∧ (e8SignStab1.passing e8Certificate).length ≤ 1
    ∧ e8SignStab2.check e8Certificate = true ∧ (e8SignStab2.passing e8Certificate).length ≤ 1 := by
  exact ⟨CertificateChecks.Batch3952.e8SignOrbit_check_0, CertificateChecks.Batch3952.e8SignStab0_check_1,
    CertificateChecks.Batch3952.e8SignStab0_passing_2, CertificateChecks.Batch3952.e8SignStab1_check_3,
    CertificateChecks.Batch3952.e8SignStab1_passing_4, CertificateChecks.Batch3952.e8SignStab2_check_5,
    CertificateChecks.Batch3952.e8SignStab2_passing_6⟩

end Certificates
