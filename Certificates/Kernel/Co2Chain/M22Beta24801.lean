module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.Monster.Code.Defs
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

namespace CertificateChecks.KernelCo2Chain.M22Beta

open CFSG.EvenSporadicStandard.M22Std.OutCheck

set_option maxRecDepth 1000000

theorem check : CFSG.ComponentClassification.RankTwoSporadic.M22.autA betaArr = true := by
  decide +kernel

end CertificateChecks.KernelCo2Chain.M22Beta

end
