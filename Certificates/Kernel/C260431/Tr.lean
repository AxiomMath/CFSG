module

public import Certificates.Data.Kernel.B45Nor.Defs
public import Certificates.Data.SmithB45MatIndM23
public import Certificates.Kernel.C260431.Data

public section

namespace CFSG.KD.C260431

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

theorem tr44aA : trChk m23S44aA m23S44aAT 0 = true := by decide +kernel

theorem tr44aB : trChk m23S44aB m23S44aBT 0 = true := by decide +kernel

theorem tr44bA : trChk m23S44bA m23S44bAT 0 = true := by decide +kernel

theorem tr44bB : trChk m23S44bB m23S44bBT 0 = true := by decide +kernel

theorem tr120A : trChk m23S120A m23S120AT 0 = true := by decide +kernel

theorem tr120B : trChk m23S120B m23S120BT 0 = true := by decide +kernel

end CFSG.KD.C260431
