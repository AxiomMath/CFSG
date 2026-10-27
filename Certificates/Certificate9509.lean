module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeData
public import CFSG.RankThree.Asc83Table.MatFacts
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Sporadic.Fi24Tc.Glue

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.Blueprint in
theorem certificate9509 : 2 ≤ tcNregs ∧ tcProg.all (Op.lt tcNregs) = true ∧ tcSpec.wf = true ∧
    tcSpec.rA < tcNregs ∧ tcSpec.rB < tcNregs ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg tcSpec.rA =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1 ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg tcSpec.rB =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2 ∧
    ∀ f ∈ tcSpec.facts.take 170, f.Holds
      (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
        (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) tcProg) tcNregs := CFSG.KD.Fi24Tc.head

end Certificates
