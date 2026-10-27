module

public import Certificates.Kernel.C48M22Stab.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.C48M22

theorem all : CFSG.KC.MiscCoset.Act.allR (nat_lit 0) (nat_lit 660) (CFSG.KC.MiscCoset.Act.pointOK CFSG.KAct.C48M22.A (nat_lit 2) (nat_lit 660) CFSG.KAct.C48M22.rels) = true := by
  allR_blocks 32

theorem fix0 : CFSG.KC.MiscCoset.Act.relsAt CFSG.KAct.C48M22.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.C48M22.fix (nat_lit 0) = true := by quickRfl

theorem moves : CFSG.KC.MiscCoset.Act.movesOK CFSG.KAct.C48M22.A (Nat.add (nat_lit 2) (nat_lit 2)) CFSG.KAct.C48M22.move = true := by quickRfl

end CFSG.KAct.C48M22

end
