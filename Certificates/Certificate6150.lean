module

public import CFSG.LocalAnalysis.OddStandard.ONanB2MirrorFacts
import Certificates.Kernel.ONanMirror.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.CM in
theorem certificate6150 : MirrorFactsP ∧ (∀ r ∈ relsM, FreeGroup.lift gen2Perm r = 1) ∧ MirrorChainP :=
  ⟨ONanMirror.mirror_facts, ONanMirror.mirror_rels, ONanMirror.mirror_chainP⟩

end Certificates
