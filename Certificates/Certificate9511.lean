module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeData
public import CFSG.RankThree.Asc83Table.MatFacts
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Sporadic.Fi24Cp.Glue

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.Blueprint in
theorem certificate9511 : (2 ≤ cpNregs ∧ cpProg.all (Op.lt cpNregs) = true ∧ cpSpec.wf = true ∧
    cpSpec.rA < cpNregs ∧ cpSpec.rB < cpNregs ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg cpSpec.rA =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1 ∧
    slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
      (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg cpSpec.rB =
        NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2 ∧
    ∀ f ∈ cpSpec.facts, f.Holds
      (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
        (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) cpProg) cpNregs) ∧
    (cpSpec.noFun = true) :=
  ⟨CFSG.KD.Fi24Cp.cp_ok, CFSG.KD.Fi24Cp.nofun_ok⟩

end Certificates
