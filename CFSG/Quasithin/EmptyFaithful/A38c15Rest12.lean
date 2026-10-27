module

public import CFSG.Quasithin.EmptyFaithful.A38c15Sl3
public import CFSG.Quasithin.EmptyFaithful.A38c14A312Rest11

public section

namespace CFSG.Quasithin.A38c15

open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest12 : Prop where
  gl2 : GL2OddIndex
  sl3 : SL3OddIrr
  u3odd : FamU3odd
  su3odd : FamSl3oddMinus
  m23 : FamM23
  m24 : FamM24
  j1 : FamJ1
  j2 : FamJ2
  j4 : FamJ4
  hs : FamHs
  he : FamHe
  ru : FamRu

theorem A312ResidualRest12.toRest11 (h : A312ResidualRest12) : A38c14.A312ResidualRest11 :=
  ⟨famL3odd_of h.gl2 h.sl3, h.u3odd, h.m23, h.m24, h.j1, h.j2, h.j4, h.hs, h.he, h.ru,
    famSl3odd_of (famSl3oddPlus_of h.gl2 h.sl3) h.su3odd⟩

theorem A312ResidualRest12.toRest
    (h : A312ResidualRest12) :
    A38c14.A312ResidualRest :=
  h.toRest11.toRest

end CFSG.Quasithin.A38c15
