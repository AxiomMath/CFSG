module

public import CFSG.Quasithin.EmptyFaithful.A38c14A312
public import CFSG.Quasithin.EmptyFaithful.A38c14Hat7
public import CFSG.Quasithin.EmptyFaithful.A38c14HatM22

public section

namespace CFSG.Quasithin.A38c14

open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest11 : Prop where
  l3odd : FamL3odd
  u3odd : FamU3odd
  m23 : FamM23
  m24 : FamM24
  j1 : FamJ1
  j2 : FamJ2
  j4 : FamJ4
  hs : FamHs
  he : FamHe
  ru : FamRu
  sl3odd : FamSl3odd

theorem A312ResidualRest11.toRest
    (h : A312ResidualRest11) :
    A312ResidualRest :=
  ⟨h.l3odd, h.u3odd, h.m23, h.m24, h.j1, h.j2, h.j4, h.hs, h.he, h.ru, h.sl3odd, hat7, hatM22⟩

end CFSG.Quasithin.A38c14
