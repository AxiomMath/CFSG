module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Recognition.M12AmalAutCheck

public section

open CFSG CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

namespace CertificateChecks.Batch17039

open CFSG CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

private theorem bA_eq_m12A1_0 :  bA = m12A1  := by
  decide +kernel

private theorem bB_eq_m12B1_1 :  bB = m12B1  := by
  decide +kernel

private theorem bS_eq_m12Sigma_2 :  bS = m12Sigma  := by
  decide +kernel

end CertificateChecks.Batch17039

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier in
theorem certificate17039 : (
 bA = m12A1 
)
    ∧ (
 bB = m12B1 
)
    ∧ (
 bS = m12Sigma 
) := by
  exact ⟨@CertificateChecks.Batch17039.bA_eq_m12A1_0, @CertificateChecks.Batch17039.bB_eq_m12B1_1, @CertificateChecks.Batch17039.bS_eq_m12Sigma_2⟩

end Certificates
