
module

public import Certificates.Data.Yosh26900Spec
import Certificates.Kernel.Yosh26900.Glue
import Certificates.Kernel.YoshQ.GlueRec

public section

namespace Certificates

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b
open CertificateChecks.KernelYoshQ

theorem certificate26900 : CFSG.EvenSporadicStandard.M12Std.Yosh.Spec.Facts ∧
    CFSG.EvenSporadicStandard.Fin76b.EnumSpec 14
      CFSG.EvenSporadicStandard.M12Std.Yosh.yGens CFSG.EvenSporadicStandard.M12Std.Yosh.yEl ∧
    CFSG.EvenSporadicStandard.M12Std.Yosh.yEl.size = 384 :=
  ⟨CFSG.KD.Yosh26900.spec_facts,
    CFSG.EvenSporadicStandard.Fin76b.enumOK_spec (by norm_num)
      (y_ok.enumOK (size := 384) (by decide) (by decide) (by decide) (Nat.le_refl _)
        (gensOK_spec g_y).2 (by decide))⟩

end Certificates
