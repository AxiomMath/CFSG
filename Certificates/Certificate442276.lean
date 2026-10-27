module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CPair
import Certificates.Kernel.Misc.A6C5Cent.Chk
import CFSG.Certificates.Kernel.Misc.A6C5CentSound

public section

namespace Certificates

theorem certificate442276 : ∀ (Γ : Type) [Group Γ], CFSG.OddStandard.SmallF3.Omega.A6CModel 5 Γ →
    CFSG.OddStandard.SmallF3.Omega.A6CPairFacts Γ (fun _ => True) 10 2 :=
  CFSG.KS.A6C5.a6c5_facts CFSG.KD.A6C5.basic_ok CFSG.KD.A6C5.candA0 CFSG.KD.A6C5.candA1
    CFSG.KD.A6C5.candA2

end Certificates
