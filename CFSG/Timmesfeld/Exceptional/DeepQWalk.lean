module

public import Certificates.Certificate8055

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.CosetTable

theorem walk :
    PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk} (FreeGroup.mk wQC6) ∈
      genSub {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk} (subsetOf 3 [0, 1]) :=
  Certificates.certificate8055

end CFSG.Timmesfeld.Moufang.Deep
