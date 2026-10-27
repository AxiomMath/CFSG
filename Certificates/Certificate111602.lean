module

public import CFSG.RankThree.PartTwo.J2Residue.C4725Module
public import CFSG.RankThree.PartTwo.J2Residue.H2Transfer
import Certificates.Kernel.J2H2.Glue
import Certificates.Kernel.J2H2.Final

public section

open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue in
theorem certificate111602 : ∀
    (ρ : ↥P →* Module.End (ZMod 2) (Fin 12 → ZMod 2)),
    (∀ (j : ℕ) (v : Fin 12 → ZMod 2), ρ (letterP j) v = (C4725.Mj j).mulVec v) →
    ∀ c : ↥P → ↥P → (Fin 12 → ZMod 2), H2.IsNormCoc ρ c → ∃ β, c = H2.cob ρ β :=
  J2H2.certificate111602_of_res J2H2.res_cob_J2

end Certificates
