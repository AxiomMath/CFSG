module

public import CFSG.Quasithin.Background.HMathieuMask
public meta import CFSG.Quasithin.Background.HMathieuMask
public meta import CFSG.Monster.Code.Basis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public meta import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public meta import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public meta import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public meta import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public meta import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public meta import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public meta import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public meta import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public meta import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public meta import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def invArr (a : Array ℕ) : Array ℕ :=
  (List.range 24).foldl (fun b i => b.set! a[i]! i) (Array.replicate 24 0)

@[expose] def inAutOK (a : Array ℕ) : Bool :=
  InvPairOK 24 a (invArr a) && autArrOK a (invArr a)

@[expose] def cent22H : List (Array ℕ) :=
  [#[0, 1, 2, 16, 22, 8, 14, 5, 3, 18, 17, 19, 6, 12, 9, 21, 11, 15, 20, 7, 13, 23, 10, 4],
    #[0, 1, 2, 12, 3, 15, 14, 13, 20, 5, 18, 10, 8, 19, 7, 23, 16, 9, 21, 6, 4, 22, 11, 17]]

@[expose] def cent22S : List (Array ℕ) :=
  [#[0, 1, 9, 5, 22, 6, 11, 20, 19, 10, 16, 7, 2, 15, 23, 17, 3, 18, 21, 14, 12, 8, 13, 4],
    #[0, 1, 7, 2, 20, 11, 15, 16, 6, 5, 3, 4, 22, 9, 13, 18, 12, 8, 19, 23, 14, 21, 10, 17],
    #[0, 1, 19, 13, 10, 18, 8, 14, 22, 16, 12, 20, 11, 21, 5, 2, 4, 17, 15, 7, 9, 6, 23, 3],
    #[0, 1, 8, 15, 12, 10, 17, 16, 9, 14, 6, 7, 23, 22, 11, 13, 3, 19, 5, 20, 21, 4, 2, 18],
    #[0, 1, 20, 17, 21, 5, 16, 4, 13, 2, 6, 8, 11, 19, 23, 10, 7, 12, 9, 3, 22, 15, 14, 18],
    #[0, 1, 16, 9, 3, 4, 22, 15, 10, 19, 7, 5, 12, 21, 2, 6, 13, 11, 14, 17, 18, 20, 23, 8],
    #[0, 1, 21, 10, 12, 4, 19, 3, 18, 16, 22, 11, 14, 7, 2, 17, 15, 20, 13, 9, 6, 23, 8, 5],
    #[0, 1, 14, 4, 5, 11, 15, 10, 9, 20, 19, 2, 22, 6, 13, 21, 17, 8, 3, 23, 7, 18, 16, 12],
    #[0, 1, 4, 13, 5, 9, 12, 8, 16, 10, 2, 23, 19, 7, 15, 17, 3, 18, 20, 11, 14, 21, 22, 6],
    #[0, 1, 18, 10, 6, 17, 9, 4, 3, 15, 7, 23, 11, 21, 16, 22, 19, 14, 8, 13, 5, 12, 2, 20]]

@[expose] def swap01Arr : Array ℕ :=
  #[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] def cent11H : List (Array ℕ) :=
  [#[0, 1, 23, 17, 6, 7, 16, 22, 2, 5, 15, 9, 3, 4, 8, 14, 12, 13, 18, 21, 10, 11, 19, 20],
    #[0, 1, 7, 5, 15, 21, 12, 22, 16, 19, 9, 10, 23, 14, 13, 20, 8, 18, 11, 17, 4, 2, 3, 6]]

@[expose] def cent11S : List (Array ℕ) :=
  [#[0, 20, 17, 5, 16, 1, 21, 4, 18, 23, 6, 3, 8, 9, 14, 10, 15, 11, 13, 12, 2, 7, 22, 19],
    #[0, 12, 21, 23, 13, 1, 18, 17, 14, 3, 7, 6, 15, 2, 11, 10, 20, 19, 5, 9, 22, 16, 8, 4],
    #[0, 22, 8, 18, 12, 6, 3, 1, 20, 21, 13, 5, 10, 17, 23, 2, 14, 11, 9, 4, 16, 15, 19, 7],
    #[0, 1, 14, 12, 4, 16, 7, 18, 8, 11, 21, 20, 19, 6, 5, 17, 22, 9, 23, 10, 15, 3, 2, 13],
    #[0, 13, 18, 1, 5, 15, 6, 16, 2, 7, 9, 22, 8, 10, 19, 14, 23, 21, 17, 12, 3, 4, 20, 11],
    #[0, 8, 22, 13, 19, 2, 3, 4, 18, 5, 20, 21, 9, 6, 10, 16, 23, 1, 15, 11, 12, 7, 17, 14],
    #[0, 3, 17, 16, 4, 6, 13, 12, 15, 14, 7, 5, 19, 18, 1, 2, 21, 9, 10, 23, 8, 20, 11, 22],
    #[0, 5, 21, 17, 16, 20, 1, 4, 11, 14, 22, 23, 18, 19, 10, 15, 3, 2, 8, 12, 13, 9, 7, 6],
    #[0, 15, 22, 13, 3, 7, 6, 20, 12, 4, 18, 10, 8, 11, 1, 23, 5, 14, 19, 9, 16, 17, 21, 2],
    #[0, 2, 16, 8, 17, 7, 4, 9, 5, 22, 1, 14, 20, 19, 21, 10, 18, 12, 11, 13, 15, 6, 23, 3],
    #[0, 21, 2, 15, 18, 1, 8, 4, 20, 6, 14, 5, 7, 19, 3, 9, 22, 16, 17, 13, 10, 11, 23, 12]]

@[expose] def pairImg11 (i j : ℕ) : ℕ := actM ccECols (pairMask i j)

end CFSG.Quasithin.H.Mathieu
