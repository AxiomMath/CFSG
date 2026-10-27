module

public import CFSG.Quasithin.EmptyFaithful.A38c17Rest4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Main

public section

namespace CFSG.Quasithin.A38c17

open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest3 : Prop where
  su3Irr : SU3OddIrr
  m24 : FamM24
  j4 : FamJ4

theorem A312ResidualRest3.toRest4
    (h : A312ResidualRest3) : A312ResidualRest4 :=
  ⟨h.su3Irr, A312M23.famM23_holds, h.m24, h.j4⟩

end CFSG.Quasithin.A38c17
