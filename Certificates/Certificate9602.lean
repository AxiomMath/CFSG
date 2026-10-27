module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data
public import CFSG.RankThree.Asc83Table.MatFacts
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Sporadic.Fi24Alpha.Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi24 CFSG.Blueprint in
theorem certificate9602 : 2 ≤ fi24Nregs ∧ fi24Prog.all (Op.lt fi24Nregs) = true ∧
    (∀ f ∈ fi24Mod.modFactsW 3 fi24Tops, f.Holds
      (slpRegs (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed1)
        (NativeSporadic.decode 3 781 1 NativeSporadic.Fi24primeSeed2) fi24Prog) fi24Nregs) ∧
    fi24Mod.wfO 3 fi24Orb = true ∧ pcWf (fi24Tops ++ fi24Mod.basisPc 3) = true ∧
    fi24Tops.all (fun g => fi24Mod.acts.any (·.reg == g.reg)) = true ∧
    fi24Mod.wOK 3 fi24Tops fi24Tidx 16 = true ∧ 3 ≤ fi24Mod.basis.length ∧
    fi24Mod.funOK 3 fi24Cf = true ∧ fi24Mod.altOK 3 fi24Ci fi24Ct tgtAlt = true := CFSG.KD.Fi24Alpha.mod_ok

end Certificates
