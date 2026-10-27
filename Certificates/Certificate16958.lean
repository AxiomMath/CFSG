module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs
import Certificates.Certificate6007
import Certificates.Certificate10127
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
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen in
theorem certificate16958 :
    gw vW13 * gw genD13W1 = gw genD13W1 * gw vW13 ∧
      gw vW13 * gw genD13W0 ^ 6 * gw vW13 * gw genD13W0 ^ 7 = gw genD13W0 ∧
      gw vW13 * gw genD13W2 ^ 6 * gw vW13 * gw genD13W2 ^ 7 = gw genD13W2 * gw genD13W1 ^ 4 ∧
      gw tW13 * gw tW13 = 1 ∧ gw vW13 * gw tW13 = gw tW13 * gw vW13 ∧
      gw tW13 * gw genD13W1 * gw tW13 * gw genD13W1 = 1 ∧
      gw bW13 * gw tW13 = gw tW13 * gw bW13 ∧
      gw bpW13 * gw vtW13 = gw vtW13 * gw bpW13 ∧
      gw wvW13 ^ 4 = 1 ∧ gw vW13 * gw wvW13 = gw wvW13 * gw vW13 ∧
      gw genD13W1 * gw wvW13 = gw wvW13 * gw genD13W1 ∧
      gw wtW13 ^ 4 = 1 ∧ gw tW13 * gw wtW13 = gw wtW13 * gw tW13 ∧
      gw bW13 * gw wtW13 = gw wtW13 * gw bW13 ∧
      gw wtW13 * gw genD13W1 = gw genD13W1 ^ 8 * gw wtW13 ∧
      gw wvtW13 ^ 4 = 1 ∧ gw vtW13 * gw wvtW13 = gw wvtW13 * gw vtW13 ∧
      gw bpW13 * gw wvtW13 = gw wvtW13 * gw bpW13 ∧
      gw wvtW13 * gw genD13W1 = gw genD13W1 ^ 8 * gw wvtW13 ∧
      gw htW13 * gw tW13 = gw vW13 * gw htW13 ∧ gw hvtW13 * gw vtW13 = gw vW13 * gw hvtW13 ∧
      gw tW13 ≠ 1 ∧ gw vtW13 ≠ 1 ∧ gw bW13 ≠ 1 ∧ gw bpW13 ≠ 1 ∧
      gw wvW13 * gw wvW13 ≠ 1 ∧ gw wtW13 * gw wtW13 ≠ 1 ∧ gw wvtW13 * gw wvtW13 ≠ 1 := KernelKDenseP.M13.facts16958

end Certificates
