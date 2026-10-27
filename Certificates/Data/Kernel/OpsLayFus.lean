module

public import Certificates.Data.Kernel.OpsLayMcert
public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] noncomputable def fusL (c : Lay) (A B nregs : Nat) (prog : List Op)
    (D : CFSG.RankThree.PartOne.CTP.Fus.Spec) : Bool :=
  seedsL c A B ⟨nregs, prog, D.facts⟩ D.rA D.rB && D.wf

end CFSG.KC.OpsLayK

end
