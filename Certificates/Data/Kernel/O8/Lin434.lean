module

public import Certificates.Data.Item434OmegaMinus
public import Certificates.Data.Kernel.O8.Nat8

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus

@[expose] noncomputable def linK (NS NI : Nat) (cols : List Nat) : Nat :=
  orN (nat_lit 136) fun i => Nat.shiftLeft (nsMap NS NI (linApply cols) i) (Nat.mul (nat_lit 8) i)

@[expose] noncomputable def linLtK (NS : Nat) (cols : List Nat) : Bool :=
  allN (nat_lit 136) fun i => Nat.blt (linApply cols (fget NS i (nat_lit 8))) (nat_lit 256)

end CFSG.KC.O8

end
