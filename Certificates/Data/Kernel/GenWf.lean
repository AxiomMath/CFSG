module

public import Certificates.Data.Inputs2711eGen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

@[expose] def genWf (p : Nat) (D : GenData) : Bool :=
  D.gens.all (fun g => g.ord % p != 0 && g.fixes.all fun f => D.fixOrd.any (·.1 == f)) &&
    derWf (D.gens.map (·.reg)) D.der &&
    (D.wA ++ D.wB).all (fun q => D.gens.any (·.reg == q.1) || D.der.any (·.reg == q.1))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
