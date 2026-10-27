module

public import Certificates.Data.Th687.SplitTNative
public import Certificates.Data.G23RecogNativeInputs
import Certificates.Kernel.G2Three.RecogFinal

public section

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Sporadic.Th.Recog in
theorem certificate687007 :
    evalCode (z0Word ++ z0Word) = CFSG.RankThree.PartTwo.Census.Carrier.G2Three.one14 ∧
    evalCode z0Word ≠ CFSG.RankThree.PartTwo.Census.Carrier.G2Three.one14 ∧
    (∀ i : Fin 5, evalCode (z0Word ++ [(Fin.castSucc i, true)]) =
      evalCode ((Fin.castSucc i, true) :: z0Word)) ∧
    (∀ r ∈ g23PD, evalCode (CFSG.GH74.QTGen4.Recog.G23.substWord (dEmbed r)) = CFSG.RankThree.PartTwo.Census.Carrier.G2Three.one14) ∧
    evalCode (CFSG.GH74.QTGen4.Recog.G23.substWord d2mWord) ≠ CFSG.RankThree.PartTwo.Census.Carrier.G2Three.one14 ∧
    evalCode (CFSG.GH74.QTGen4.Recog.G23.substWord (List.flatten (List.replicate 7 d2mWord))) = CFSG.RankThree.PartTwo.Census.Carrier.G2Three.one14 := CFSG.KD.G2Three.ok687007

end Certificates
