module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutGrp
import Certificates.Kernel.Asc82Syl.Final

public section

namespace Certificates

theorem certificate442274 : CFSG.OddStandard.SmallF3.Omega.FFRAGroup 512 CFSG.OddStandard.SmallF3.Omega.ffRADPlus
      false 32 ∧
    CFSG.OddStandard.SmallF3.Omega.FFRAGroup 1024 CFSG.OddStandard.SmallF3.Omega.ffRADMinus
      true 32 :=
  ⟨CFSG.KS.Asc82Syl.a82_groupP, CFSG.KS.Asc82Syl.a82_groupM⟩

end Certificates
