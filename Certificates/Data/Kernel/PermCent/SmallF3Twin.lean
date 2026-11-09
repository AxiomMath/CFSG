module

public import Certificates.Data.Kernel.PermCent.SmallF3TwinBase
public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T

@[expose] noncomputable def cent3OddAllC (LA LP : List (CV 28)) : Bool :=
  LP.all fun g => !(decide (g * g * g = 1) && !decide (g = 1)) ||
    (LP.filter fun x => eq22C g x x g).length % 2 == 1 ||
    LA.all fun σ => !(powOneC σ 2 && eq22C σ g g σ) || siftC CFSG.GH74.KGroups.U33.QP σ 0

end CFSG.Certificates.Kernel.PkCV.SmallF3T

end
