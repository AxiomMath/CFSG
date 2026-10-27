module

public import Certificates.Data.Kernel.A6CK.Defs
public import Certificates.Kernel.A6CK.Data

public section

namespace CFSG.KD.A6CK

open CFSG.KC.A6CK

set_option maxRecDepth 100000

theorem ch442277_const : constK a0 g0 tau n0 r0 = true := by decide +kernel
theorem ch442277_gens : gensK G GT = true := by decide +kernel
theorem ch442277_ea : centGensK EA a0 = true := by decide +kernel
theorem ch442277_et : centGensK ET tau = true := by decide +kernel
theorem ch442277_A : walkK (conjStepK G GT) 8 a0 2835 A.E A.C = true := by decide +kernel
theorem ch442277_Ad : nodupK A.E = true := by decide +kernel
theorem ch442277_CA : walkK (leftStepK EA) 6 IDK 9216 CA.E CA.C = true := by decide +kernel
theorem ch442277_CAd : nodupK CA.E = true := by decide +kernel
theorem ch442277_T : walkK (conjStepK G GT) 8 tau 4536 T.E T.C = true := by decide +kernel
theorem ch442277_Td : nodupK T.E = true := by decide +kernel
theorem ch442277_CT : walkK (leftStepK ET) 6 IDK 5760 CT.E CT.C = true := by decide +kernel
theorem ch442277_CTd : nodupK CT.E = true := by decide +kernel
theorem ch442277_F : walkK (conjStepK G GT) 8 r0 252 F.E F.C = true := by decide +kernel
theorem ch442277_Fd : nodupK F.E = true := by decide +kernel
theorem ch442277_k0 : k0K g0 CT.E K0 = true := by decide +kernel
theorem ch442277_pairs : pairsAK g0 K0 F.E A.E KA = true := by decide +kernel

end CFSG.KD.A6CK
