module

public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankDefs

public section

namespace CFSG.KC.OpsMN

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3

@[expose] noncomputable def coreGenN {V : Type} (O : Ops Nat V) (A B nregs : Nat) (prog : List Op)
    (D : RSpec) : Bool :=
  regsN O A B nregs prog fun R => certN O R ⟨nregs, prog, D.facts⟩ &&
    O.eq (getN R D.rA) A && O.eq (getN R D.rB) B

end CFSG.KC.OpsMN

end
