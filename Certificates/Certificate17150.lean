module

public import CFSG.Certificates.Kernel.BabyMonster.BThirteenFacts
public import CFSG.Certificates.Kernel.BabyMonster.RegRun
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Data3
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Data4
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Data5
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenInputs
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.BThirteen.Facts
import Certificates.Kernel.BabyMonster.BThirteen.Regs
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
public import CFSG.Open.Defs
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.BM CFSG.Blueprint.NativeSporadic
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native in
theorem certificate17150 : decode 2 4370 1 BSeed1 = stripMat Seeds.A1 ∧ decode 2 4370 1 BSeed2 = stripMat Seeds.A2 ∧
    Reg.RegsOK (b13Prog ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true
      [31, 32, 44, 45, 46, 81] [BThirteen.X, BThirteen.S, BThirteen.T2, BThirteen.T4,
        BThirteen.T5, BThirteen.G] ∧
    BThirteen.Fact17150 (stripMat BThirteen.X) (stripMat BThirteen.S) (stripMat BThirteen.T2)
      (stripMat BThirteen.T4) (stripMat BThirteen.T5) (stripMat BThirteen.G) :=
  ⟨KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat, KernelBM.BThirteen.b13_regs,
    KernelBM.BThirteen.fact17150⟩

end Certificates
