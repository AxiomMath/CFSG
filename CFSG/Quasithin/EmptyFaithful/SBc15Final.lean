module

public import CFSG.Quasithin.EmptyFaithful.SBc15C2
public import CFSG.Quasithin.EmptyFaithful.SBc15R3
public import CFSG.Quasithin.EmptyFaithful.SBc15F5
public import CFSG.Quasithin.EmptyFaithful.SBc15F3

public section

namespace CFSG.Quasithin

namespace SBc15

theorem input14616Weak_of_weakW (h5 : WeakW (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5)))
    (h3 : WeakW (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ⊤) : Input14616Weak :=
  input14616Weak_of_parabolic input14616ParabolicTwo_proved (input14616ParabolicThreeA_of_weakW h5)
      (input14616ParabolicThreeB_of_weakW h3)

theorem input14616Weak_proved : Input14616Weak :=
  input14616Weak_of_weakW weakW_five weakW_l32

end SBc15

end CFSG.Quasithin
