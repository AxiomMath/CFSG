module

public import Certificates.Data.TripleCoverSuz

public section

open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.Native

namespace CertificateChecks.Batch8006

open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.Native

private theorem suz_gen_check_0 : genOK = true := by
  decide +kernel

private theorem suz_rels_check_1 : relsOK = true := by
  decide +kernel

private theorem suz_config_check_2 : configOK = true := by
  decide +kernel

end CertificateChecks.Batch8006

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.Native in
theorem certificate8006 : genOK = true ∧ relsOK = true ∧ configOK = true := by
  exact ⟨CertificateChecks.Batch8006.suz_gen_check_0, CertificateChecks.Batch8006.suz_rels_check_1, CertificateChecks.Batch8006.suz_config_check_2⟩

end Certificates
