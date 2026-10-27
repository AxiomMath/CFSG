module

public import CFSG.Quasithin.EmptyFaithful.A38c17Rest7
public import CFSG.Quasithin.EmptyFaithful.A38c17Red

public section

namespace CFSG.Quasithin.A38c17

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.A38c15

structure A312ResidualRest6 : Prop where
  su3Irr : SU3OddIrr
  m23 : FamM23
  m24 : FamM24
  j4 : FamJ4
  hs : FamHs
  he : FamHe

theorem A312ResidualRest6.toRest7 (h : A312ResidualRest6) :
    A312ResidualRest7 :=
  ⟨famU3odd_of (su3ReducibleOdd gl2OddIndex) h.su3Irr,
    famSl3oddMinus_of (su3ReducibleOdd gl2OddIndex) h.su3Irr, h.m23, h.m24, h.j4, h.hs, h.he⟩

theorem A312ResidualRest6.toRest10
    (hj2 : FamJ2) (h : A312ResidualRest6) : A38c15.A312ResidualRest10 :=
  h.toRest7.toRest10 hj2

end CFSG.Quasithin.A38c17
