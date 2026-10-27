module

public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QT2LocZProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem centralizer_z0_not_le_Hj :
    ∃ g : J, g * eta uJ 11 1131 = eta uJ 11 1131 * g ∧ g ∉ Hj :=
  exists_centralizer_not_mem_Hj j4Facts

end CFSG.Sporadic.J4.QT2
