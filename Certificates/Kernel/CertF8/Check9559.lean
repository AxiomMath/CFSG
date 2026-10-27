module

public import Certificates.Data.Kernel.CertF8.Pack
public import Certificates.Data.Kernel.CertF8.SU9559
public import Certificates.Data.ONanG28SU

public section

namespace Certificates.Kernel.CertF8

open CFSG.KC.CertF8 CFSG.KC.G28 CFSG.AGLEmbedding.KFactProofs.G28 CFSG.AGLEmbedding.KFactProofs.G28.SU

theorem ch9559P : mulS6 (codeP suP) (codeP suPi) = idP ∧ mulS6 (codeP suPi) (codeP suP) = idP := by
  decide +kernel

theorem ch9559R : mulS6 (mulS6 (codeP suPi) (powS6 (wordS6 tUW) 3)) (codeP suP) = codeP rCode := by
  decide +kernel

theorem ch9559A : ∀ k : Fin 7,
    mulS6 (mulS6 (codeP suPi) (wordS6 suW[k.val]!)) (codeP suP) = codeP aCodes[k.val]! := by
  decide +kernel

theorem ch9559W : wordS6 suW[5]! = codeP w5Code := by
  decide +kernel

end Certificates.Kernel.CertF8

end
