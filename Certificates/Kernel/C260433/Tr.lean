module

public import Certificates.Data.Kernel.B45Nor.Defs
public import Certificates.Data.SmithB45MatIndM24
public import Certificates.Kernel.C260433.Data

public section

namespace CFSG.KD.C260433

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

theorem tr44aA : trChk m24S44aA m24S44aAT 0 = true := by decide +kernel

theorem tr44aB : trChk m24S44aB m24S44aBT 0 = true := by decide +kernel

theorem tr44bA : trChk m24S44bA m24S44bAT 0 = true := by decide +kernel

theorem tr44bB : trChk m24S44bB m24S44bBT 0 = true := by decide +kernel

theorem tr120A : trChk m24S120A m24S120AT 0 = true := by decide +kernel

theorem tr120B : trChk m24S120B m24S120BT 0 = true := by decide +kernel

end CFSG.KD.C260433
