module

public import Certificates.Data.G23RecogTriNativeInputs
public import Certificates.Data.G23RecogNativeInputs
import Certificates.Kernel.G2Three.RecogFinal

public section

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.P7
  CFSG.RankThree.PartTwo.Census.Carrier.G2Three in
theorem certificate320014 : (∀ r ∈ triWords, evalCode (substTri r) = CFSG.RankThree.PartTwo.Census.Carrier.G2Three.one14)
    ∧ (∀ i, evalCode (substTri (triEWord i)) = CFSG.GH74.QTGen4.Recog.G23.eCode i) := CFSG.KD.G2Three.ok320014

end Certificates
