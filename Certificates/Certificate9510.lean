module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeData
public import CFSG.RankThree.Asc83Table.MatFacts
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Sporadic.Fi24Tc.Glue

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.Blueprint in
theorem certificate9510 : ∀ f ∈ tcSpec.facts.drop 170, f.Holds
    (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg) tcNregs := CFSG.KD.Fi24Tc.tail

end Certificates
