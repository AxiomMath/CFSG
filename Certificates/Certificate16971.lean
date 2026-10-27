module

public import CFSG.GF2Type.Smith1979.GammaU.FrameFixInputs
import Certificates.Kernel.GammaU.FrameFixOK
import CFSG.Certificates.Kernel.GammaUFrameFixSound

public section

open CFSG.GF2Type.Smith1979.GammaU.StepA CFSG.KD.GUX

namespace Certificates

open CFSG.GF2Type.Smith1979.GammaU.StepA in
theorem certificate16971 : frameFixCheck () = true :=
  by
    rw [frameFixCheck, CFSG.KC.GUX.frameFixAt_of ff16971_rowsG0 ff16971_rowsC0 ff16971_fix0
      ff16971_a0_0 ff16971_comm0 ff16971_wit0 ff16971_n2_0, CFSG.KC.GUX.frameFixAt_of ff16971_rowsG1
      ff16971_rowsC1 ff16971_fix1 ff16971_a0_1 ff16971_comm1 ff16971_wit1 ff16971_n2_1]
    rfl

end Certificates
