module

public import CFSG.Quasithin.EmptyFaithful.A38c17Rest3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Main

public section

namespace CFSG.Quasithin.A38c17

open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest2 : Prop where
  su3Irr : SU3OddIrr
  j4 : FamJ4

theorem A312ResidualRest2.toRest3
    (h : A312ResidualRest2) : A312ResidualRest3 :=
  ⟨h.su3Irr, A312M24.famM24_holds, h.j4⟩

end CFSG.Quasithin.A38c17
