module

public import CFSG.RankThree.PartOne.SolD3.E2
public import CFSG.RankThree.PartOne.SolD3.SzU3Indec
public import CFSG.CGT.PushingUpLit.SolK.Final

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.CGT.PushingUpLit.SolK
open CFSG.ComponentClassification.HSFLit (HaradaInput)

theorem solDegreeThreeRNe1_of (hE2 : SolomonTimmesfeldTight) (hOrd : TightSmallGroupOrders)
    (hHar : HaradaInput) (hWC3 : WCBlockCentralizerThree) : SolDegreeThreeRNe1 := by
  intro G _ _ hKP hsimple hchar M X hMmax hXM hnorm hshort hnat huniq hR
  obtain ⟨a, hb⟩ := exists_blk3 hshort hnat
  exact gen4_of_degree_three hE2 hOrd hHar hWC3 szU3SylowIndecomposable hKP
    ⟨hsimple, hchar, hMmax, hXM, hnorm, huniq, hshort, hnat⟩ hb hR

end CFSG.RankThree.PartOne.SolD3
