module

public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose
public import CFSG.Quasithin.EmptyFaithful.A38c15Rest12

public section

namespace CFSG.Quasithin.A38c15

open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest10 : Prop where
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

theorem A312ResidualRest10.toRest
    (h : A312ResidualRest10) : A38c14.A312ResidualRest :=
  (A312ResidualRest12.mk gl2OddIndex sl3OddIrr h.u3odd h.su3odd h.m23 h.m24 h.j1 h.j2 h.j4 h.hs
    h.he h.ru).toRest

end CFSG.Quasithin.A38c15
