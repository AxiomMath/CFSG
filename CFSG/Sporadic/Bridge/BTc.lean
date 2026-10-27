module

public import CFSG.Sporadic.Bridge.BTcFive
public import CFSG.Sporadic.Bridge.BTcData
public import Certificates.Certificate9726
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicRankCommData
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B.Primes.Native CFSG.AGLEmbedding

theorem tcGenDatum_B_five :
    TCGenDatum NativeSporadic.B 5 := by
  obtain ⟨hact, hu5, huq, hind, e, he0, heu, a, ha, b, hb, G, Gi, hGi, h1, h2⟩ :=
    Certificates.certificate9726
  exact tcGenDatum_B_of_facts tcHR tcHC hact hu5 huq hind e he0 heu ha hb G Gi hGi h1 h2

end CFSG.Sporadic.Bridge.B
