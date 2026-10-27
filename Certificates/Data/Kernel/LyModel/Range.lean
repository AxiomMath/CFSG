module

public import CFSG.Certificates.Kernel.MonsterConv.Perm

public section

namespace CFSG.KC.LyModel

open CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def rangeOK (n N : Nat) : Bool :=
  Nat.beq (netsApply 17 131072 1 [N] (ones n)) (ones n)

end CFSG.KC.LyModel

end
