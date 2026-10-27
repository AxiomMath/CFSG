module

public import Certificates.Data.Item434SporGenMathieu
import Certificates.Kernel.Item434.M12Facts
import Certificates.Kernel.Item434.M22Facts

public section

namespace Certificates

open CertificateChecks.KernelItem434 in
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen in
theorem certificate8035 : m12GenCheck sigAW sigAP genAa genAb = true ∧
    m12GenCheck sigA2W sigA2P genA2a genA2b = true ∧ m12FixCheck = true ∧
    (∀ v : CFSG.GH74.M12.Hyp.G12, CFSG.GH74.M12.Hyp.tbl v.1 ∈
        CFSG.RankThree.PartTwo.Toolkit.M12.ET ++ CFSG.RankThree.PartTwo.Toolkit.M12.FT → v ≠ 1 →
        Nat.card (Subgroup.centralizer ({v} : Set CFSG.GH74.M12.Hyp.G12)) = 54) ∧
    m22ChainCheck = true ∧ m22SiftCheck = true ∧ m22EltCheck = true :=
  ⟨m12_genA, m12_genA2, m12_fix, m12_cent, m22_chain, m22_sift, m22_elt⟩

end Certificates
