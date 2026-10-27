module

public import Certificates.Data.Item434SporGenJ2HSMcL
import Certificates.Kernel.Item434.HSFacts
import Certificates.Kernel.Item434.J2Facts
import Certificates.Kernel.Item434.McLFacts

public section

namespace Certificates

open CertificateChecks.KernelItem434 in
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem certificate8099 : hsChainCheck = true ∧ hsSiftCheck = true ∧ hsEltCheck = true ∧ j2ChainCheck = true ∧
    j2SiftCheck = true ∧ j2EltCheck = true ∧ mclZCheck = true ∧ mclDCheck = true ∧
    mclLineCheck = true ∧ mclConjCheck = true :=
  ⟨hs_chain, hs_sift, hs_elt, j2_chain, j2_sift, j2_elt, mcl_z, mcl_d, mcl_line, mcl_conj⟩

end Certificates
