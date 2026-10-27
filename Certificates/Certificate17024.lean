module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.M12AscCountH

public section

open CFSG CFSG.Quasithin Subgroup

namespace CertificateChecks.Batch17024

open CFSG CFSG.Quasithin Subgroup

private theorem tab_pow6_of_comm_0 :  ∀ q ∈ ascHTabs, tpow q 3 = tid → q ≠ tid →
    ∀ h ∈ ascHTabs, tmul h q = tmul q h → tpow h 6 = tid  := by
  decide +kernel

private theorem tab_cube_cases_1 :  ∀ h ∈ ascHTabs, h ∉ qTabs → tpow h 3 ∈ qTabs →
    tpow h 3 = tid ∨ tpow h 3 = zTab  := by
  decide +kernel

end CertificateChecks.Batch17024

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin Subgroup in
theorem certificate17024 : (
 ∀ q ∈ ascHTabs, tpow q 3 = tid → q ≠ tid →
    ∀ h ∈ ascHTabs, tmul h q = tmul q h → tpow h 6 = tid 
)
    ∧ (
 ∀ h ∈ ascHTabs, h ∉ qTabs → tpow h 3 ∈ qTabs →
    tpow h 3 = tid ∨ tpow h 3 = zTab 
) := by
  exact ⟨@CertificateChecks.Batch17024.tab_pow6_of_comm_0, @CertificateChecks.Batch17024.tab_cube_cases_1⟩

end Certificates
