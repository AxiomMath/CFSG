module

public import CFSG.Quasithin.EmptyFaithful.A38c15Rest10
public import CFSG.Quasithin.Background.A312SporJ1
public import CFSG.Quasithin.Background.A312SporRu

public section

namespace CFSG.Quasithin.A38c17

open CFSG.QuasithinUnique.Vol2Native.A312L

structure A312ResidualRest7 : Prop where
  u3odd : FamU3odd
  su3odd : A38c15.FamSl3oddMinus
  m23 : FamM23
  m24 : FamM24
  j4 : FamJ4
  hs : FamHs
  he : FamHe

theorem A312ResidualRest7.toRest10
    (hj2 : FamJ2) (h : A312ResidualRest7) : A38c15.A312ResidualRest10 :=
  ⟨h.u3odd, h.su3odd, h.m23, h.m24, CFSG.Quasithin.A312S.famJ1, hj2, h.j4, h.hs, h.he,
    CFSG.Quasithin.A312S.famRu⟩

end CFSG.Quasithin.A38c17
