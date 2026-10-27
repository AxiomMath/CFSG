
module

public import CFSG.Sporadic.Co1.Module.TwoBKernel
public import CFSG.Sporadic.Co1.Module.TwoBDataInputs

namespace CFSG.Sporadic.Co1.Module.TwoB

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.OddCentNative Matrix

attribute [local irreducible] rowsSB

section

end

attribute [local irreducible] rrB regsRowsB

section Kernel

open CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame CFSG.KC.Co1M
  CFSG.KC.Co1F2 Equiv

end Kernel

section KernelS

open CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame CFSG.KC.Co1M
  CFSG.KC.Co1F2

attribute [local instance] Odd.vecAct Odd.vecSMul

end KernelS

section Order

attribute [local instance] Odd.vecAct Odd.vecSMul

end Order

section KernelInter

attribute [local instance] Odd.vecAct Odd.vecSMul

end KernelInter

end CFSG.Sporadic.Co1.Module.TwoB
