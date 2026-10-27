module

public import Certificates.Data.G23RecogNativeFactsInputs
import Certificates.Kernel.G2Three.SylFinal

public section

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.RankThree.PartTwo.Census.Carrier.G2Three in
open CFSG.RankThree.PartTwo.Sec4.Item434RemG23 in
theorem certificate320002 : (∀ i, CFSG.RankThree.PartTwo.Sec4.Item434RemG23.wordCode (CFSG.GH74.QTGen4.Recog.G23.eWord i) = CFSG.GH74.QTGen4.Recog.G23.eCode i)
    ∧ (evalCode x1Word = x0c)
    ∧ (evalCode y1Word = y0c) := CFSG.KD.G2Three.ok320002

end Certificates
