module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBI2
import Certificates.Kernel.FzUT.BH2Glue

public section

namespace Certificates

open CFSG.KC.FzBMod

theorem certificate441796 : CFSG.OddStandard.SmallF3.FritzII.FzbFactsI ∧ CFSG.OddStandard.SmallF3.FritzII.FzbFactsII :=
  ⟨⟨⟨fzbFactsGen_mk true, fzbH2_of true⟩, fzbH1_of⟩, ⟨⟨fzbFactsGen_mk false, fzbH2_of false⟩,
    fzbV1_of⟩⟩

end Certificates
