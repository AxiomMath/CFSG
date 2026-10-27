module

public import Certificates.Kernel.AE7OddGen.Checks
public import CFSG.Certificates.Kernel.AE7OddGenSym

public section

namespace CFSG.KD.AE7OddGen

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
  Certificates.AE7OddGen CFSG.KC.AE7OddGenK

theorem oddGenProp_k : oddGenProp := by
  refine oddGenProp_of_base ?_
  rw [flagB, ae7g_comm, ae7g_ae, ae7g_pairs, ae7g_cycles]
  rfl

end CFSG.KD.AE7OddGen

end
