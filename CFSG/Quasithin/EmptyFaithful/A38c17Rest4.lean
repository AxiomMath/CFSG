module

public import CFSG.Quasithin.EmptyFaithful.A38c17Rest6
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312Hs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HeMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2

public section

namespace CFSG.Quasithin.A38c17

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.A38c15

structure A312ResidualRest4 : Prop where
  su3Irr : SU3OddIrr
  m23 : FamM23
  m24 : FamM24
  j4 : FamJ4

theorem A312ResidualRest4.toRest6
    (h : A312ResidualRest4) : A312ResidualRest6 :=
  ⟨h.su3Irr, h.m23, h.m24, h.j4, A312Hs.famHs_holds, A312He.famHe_holds⟩

theorem A312ResidualRest4.toRest10
    (h : A312ResidualRest4) : A38c15.A312ResidualRest10 :=
  h.toRest6.toRest10 A312J2.famJ2_holds

end CFSG.Quasithin.A38c17
