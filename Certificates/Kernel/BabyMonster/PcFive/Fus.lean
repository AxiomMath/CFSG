module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BabyMonster.PcFive
public import Certificates.Kernel.BabyMonster.PcFive.Data

public section

namespace CFSG.KC.BM.PcFiveD

open CFSG.KC.BM.PcFive

theorem tphi : phiOK () = true := by quickRfl

theorem tfus : fusOK rep 152 depth kind arg cls wit = true := by quickRfl

@[expose] noncomputable def chunks : List (List Nat) :=
  [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15]

theorem tlen : ∀ k < 16, (chunks.getD k []).length = if k < 15 then 1000 else 625 := by
  decide +kernel

end CFSG.KC.BM.PcFiveD

end
