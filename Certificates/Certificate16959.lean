module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenAInputs
import Certificates.Certificate6007
import Certificates.Certificate10127
import Certificates.Certificate125500
import Certificates.Certificate125501
import Certificates.Certificate125552
import Certificates.Certificate125553
import Certificates.Certificate125554
import Certificates.Certificate125555
import Certificates.Certificate125556
import Certificates.Certificate125557
import Certificates.Certificate125558
import Certificates.Certificate125559
import Certificates.Certificate125561
import Certificates.Kernel.KDenseP.M13
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF in
theorem certificate16959 :
    gw j1W * gw j1W = 1 ∧ gw j2W * gw j2W = 1 ∧ gw j2W * gw j1W = gw j1W * gw j2W ∧
      gw j1W * gw thirteenX = gw thirteenX * gw j1W ∧
      gw j2W * gw thirteenX = gw thirteenX * gw j2W ∧
      gw tj1W * gw j1W = gw tStarW * gw tj1W ∧ gw tj2W * gw j2W = gw tStarW * gw tj2W ∧
      gw tj12W * (gw j2W * gw j1W) = gw tStarW * gw tj12W ∧
      gw j1W ≠ 1 ∧ gw j2W ≠ 1 ∧ gw j2W * gw j1W ≠ 1 ∧
      ∀ e ∈ censusLines, gw (lineConjW e) * gw (lineRepW e) =
        gw (lineTargetW e) ^ e.lam * gw (lineConjW e) := KernelKDenseP.M13.facts16959

end Certificates
