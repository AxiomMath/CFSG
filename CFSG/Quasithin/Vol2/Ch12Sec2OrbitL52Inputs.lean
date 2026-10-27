module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep
public meta import Mathlib.Algebra.Field.ZMod
public meta import CFSG.Quasithin.Background.JonesParshallWedge
public meta import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public meta import CFSG.Monster.Code.Weights
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public meta import CFSG.Quasithin.Background.JonesParshallNatural
public meta import CFSG.Quasithin.Background.JonesParshallSmallSL
public meta import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount
public import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public meta import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis

open scoped Matrix

@[expose] def decodeV (c : ℕ) : Fin 10 → ZMod 2 := fun k => if c.testBit k then 1 else 0

@[expose] def fin5 (a : ℕ) : Fin 5 := ⟨a % 5, Nat.mod_lt _ (by norm_num)⟩

@[expose] def trSL' (t : ℕ) : G5 :=
  if h : fin5 (t / 5) = fin5 t then 1 else Matrix.SpecialLinearGroup.transvection h 1

@[expose] def l52Col : Array ℕ := #[
  1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1, 2, 4, 8, 18, 36, 72, 128, 256, 512, 1, 2, 4, 8, 17, 32,
  64, 132, 264, 512, 1, 2, 4, 8, 16, 33, 64, 130, 256, 520, 1, 2, 4, 8, 16, 32, 65, 128, 258, 516,
  1, 18, 36, 72, 16, 32, 64, 128, 256, 512, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1, 3, 4, 8, 16,
  32, 64, 160, 320, 512, 1, 2, 5, 8, 16, 32, 64, 144, 256, 576, 1, 2, 4, 9, 16, 32, 64, 128, 272,
  544, 17, 2, 132, 264, 16, 32, 64, 128, 256, 512, 3, 2, 4, 8, 16, 160, 320, 128, 256, 512, 1, 2,
  4, 8, 16, 32, 64, 128, 256, 512, 1, 2, 6, 8, 16, 48, 64, 128, 256, 768, 1, 2, 4, 10, 16, 32, 80,
  128, 256, 640, 33, 130, 4, 520, 16, 32, 64, 128, 256, 512, 5, 2, 4, 8, 144, 32, 576, 128, 256,
  512, 1, 6, 4, 8, 48, 32, 64, 128, 768, 512, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1, 2, 4, 12,
  16, 32, 96, 128, 384, 512, 65, 258, 516, 8, 16, 32, 64, 128, 256, 512, 9, 2, 4, 8, 272, 544, 64,
  128, 256, 512, 1, 10, 4, 8, 80, 32, 64, 640, 256, 512, 1, 2, 12, 8, 16, 96, 64, 384, 256, 512, 1,
  2, 4, 8, 16, 32, 64, 128, 256, 512]

@[expose] def l52Cls : Array Bool := #[
  false, true, true, true, true, true, true, true, true, true, true, true,
  true, true, true, true, true, true, true, true, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, false,
  true, true, false, false, false, false, false, false, false, false, false, false,
  true, true, false, false, false, false, true, true, false, false, false, false,
  false, false, false, false, true, true, false, false, false, false, false, false,
  true, true, false, false, false, false, false, false, true, true, false, false,
  false, false, false, false, false, false, true, true, false, false, false, false,
  true, true, false, false, false, false, false, false, false, false, false, false,
  true, true, false, false, true, true, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true, false, true, false,
  true, false, true, false, false, false, false, false, false, false, false, false,
  true, false, true, false, false, true, false, true, false, false, false, false,
  false, false, false, false, true, false, false, true, true, false, false, true,
  false, false, false, false, false, false, false, false, true, false, false, true,
  false, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, false, false, false, false, false,
  true, false, true, false, false, false, false, false, true, false, true, false,
  false, false, false, false, false, true, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true,
  false, false, false, false, true, false, false, true, false, false, false, false,
  true, false, false, true, false, false, false, false, false, true, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, true, false, false, false, false, false, false, false, false, false,
  true, false, true, false, true, false, true, false, false, false, false, false,
  false, false, false, false, false, true, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, true, false, false, false, false, false, false, false, false,
  true, false, false, true, true, false, false, true, false, false, false, false,
  false, false, false, false, false, true, true, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, false, false, false,
  false, true, false, false, false, true, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, true, false, false, true, false, false, false,
  false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false,
  false, true, false, false, false, true, false, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, false, false, false,
  false, false, true, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, true, false, false, false, false, false, false, true,
  false, false, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, true, false, false, false, false, true, false,
  false, false, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false,
  false, true, false, false, false, false, false, true, false, false, true, false,
  true, false, false, false, false, false, true, false, true, false, false, false,
  false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, true, false, false, true, false, false,
  false, false, false, true, true, false, false, false, false, false, false, true,
  true, false, false, false, false, false, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, true,
  false, true, false, false, false, false, true, false, true, false, false, false,
  false, false, true, false, false, false, true, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false,
  false, false, true, false, false, false, false, true, false, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, true,
  false, false, true, false, false, true, false, false, true, false, false, false,
  false, false, false, true, false, false, false, true, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false]

@[expose] def l52Words : Array (List ℕ) := #[
  [], [], [7, 11], [11], [8, 16], [16], [17, 7, 11], [16, 11], [9, 21], [21], [22, 7, 11],
  [21, 11], [23, 8, 16], [21, 16], [22, 17, 7, 11], [21, 16, 11], [2, 10], [10], [2, 1, 10],
  [1, 10], [10, 8, 2], [10, 2], [10, 8, 3, 2], [10, 3, 2], [16, 9, 8, 21], [19, 23, 10, 2],
  [16, 9, 8, 21, 3], [19, 23, 10, 3, 2], [23, 10, 8, 2], [23, 10, 2], [23, 10, 8, 3, 2],
  [23, 10, 3, 2], [3, 15], [15], [11, 7, 3], [15, 3], [3, 1, 15], [1, 15], [10, 7, 3, 2],
  [15, 3, 2], [11, 9, 7, 21], [14, 22, 15, 3], [22, 11, 7, 3], [22, 15, 3], [11, 9, 7, 21, 2],
  [14, 22, 15, 3, 2], [22, 10, 7, 3, 2], [22, 15, 3, 2], [17, 2, 10], [15, 10], [11, 7, 5, 3],
  [15, 5, 3], [10, 8, 5, 2], [10, 5, 2], [17, 2, 1, 10], [17, 1, 10], [11, 9, 8, 7, 21],
  [19, 17, 23, 10, 2], [13, 22, 11, 7, 3], [13, 22, 15, 3], [17, 23, 10, 8, 2], [17, 23, 10, 2],
  [14, 17, 23, 10, 8, 2], [14, 17, 23, 10, 2], [4, 20], [20], [15, 4, 3, 20], [19, 23, 15, 3],
  [10, 4, 2, 20], [14, 22, 10, 2], [10, 4, 3, 2, 20], [14, 13, 22, 10, 2], [4, 1, 20], [1, 20],
  [15, 4, 3, 20, 2], [19, 23, 15, 3, 2], [10, 4, 2, 20, 3], [14, 22, 10, 3, 2], [10, 4, 23, 2, 20],
  [14, 23, 22, 10, 2], [22, 2, 10], [20, 10], [15, 4, 3, 20, 8], [19, 23, 15, 5, 3],
  [22, 10, 8, 2], [22, 10, 2], [13, 22, 10, 8, 2], [13, 22, 10, 2], [16, 9, 8, 21, 7],
  [19, 23, 10, 5, 2], [22, 2, 1, 10], [22, 1, 10], [23, 22, 10, 8, 2], [23, 22, 10, 2],
  [22, 10, 8, 3, 2], [22, 10, 3, 2], [23, 3, 15], [20, 15], [23, 11, 7, 3], [23, 15, 3],
  [10, 4, 2, 20, 7], [14, 22, 10, 5, 2], [17, 23, 11, 7, 3], [17, 23, 15, 3], [11, 9, 7, 21, 8],
  [14, 22, 15, 5, 3], [23, 22, 11, 7, 3], [23, 22, 15, 3], [23, 3, 1, 15], [23, 1, 15],
  [23, 10, 7, 3, 2], [23, 15, 3, 2], [22, 17, 2, 10], [20, 15, 10], [23, 11, 7, 5, 3],
  [23, 15, 5, 3], [22, 10, 8, 5, 2], [22, 10, 5, 2], [19, 13, 22, 10, 8, 2], [19, 13, 22, 10, 2],
  [11, 9, 23, 7, 21], [19, 23, 22, 10, 2], [22, 11, 7, 5, 3], [22, 15, 5, 3], [23, 10, 8, 5, 2],
  [23, 10, 5, 2], [22, 17, 2, 1, 10], [22, 17, 1, 10], [8, 16, 2, 10], [], [15, 7, 11], [3],
  [8, 16, 10], [2], [8, 16, 1, 10], [3, 2], [9, 21], [21], [9, 21, 3], [21, 3], [9, 21, 2],
  [21, 2], [9, 21, 3, 2], [21, 3, 2], [16, 2, 10], [8], [15, 2, 1, 10], [5, 3], [8, 2], [16, 10],
  [8, 3, 2], [16, 1, 10], [9, 8, 21], [8, 21], [9, 8, 21, 3], [8, 21, 3], [8, 21, 2], [19, 8, 21],
  [8, 21, 3, 2], [19, 8, 21, 3], [3, 15, 11], [7], [7, 3], [15, 11], [8, 16, 15, 10], [5, 2],
  [7, 3, 2], [1, 15, 11], [9, 7, 21], [7, 21], [7, 21, 3], [14, 7, 21], [9, 7, 21, 2], [7, 21, 2],
  [7, 21, 3, 2], [14, 7, 21, 2], [3, 15, 1, 10], [8, 7], [7, 5, 3], [15, 1, 10], [8, 5, 2],
  [16, 15, 10], [2, 15, 1, 10], [5, 3, 2], [9, 8, 7, 21], [8, 7, 21], [8, 7, 21, 3],
  [14, 8, 7, 21], [8, 7, 21, 2], [19, 8, 7, 21], [14, 8, 7, 21, 2], [13, 7, 21, 2], [4, 20], [20],
  [4, 3, 20], [3, 20], [4, 2, 20], [2, 20], [4, 3, 2, 20], [3, 2, 20], [4, 1, 20], [1, 20],
  [4, 3, 1, 20], [3, 1, 20], [4, 2, 1, 20], [2, 1, 20], [4, 3, 2, 1, 20], [3, 2, 1, 20],
  [4, 20, 8], [20, 8], [4, 3, 20, 8], [3, 20, 8], [2, 20, 8], [14, 2, 20], [3, 2, 20, 8],
  [14, 3, 2, 20], [8, 4, 1, 20], [8, 1, 20], [4, 5, 21, 3], [5, 21, 3], [8, 2, 1, 20],
  [14, 3, 2, 1, 20], [2, 5, 21, 3], [14, 2, 1, 20], [4, 20, 7], [20, 7], [3, 20, 7], [19, 3, 20],
  [4, 2, 20, 7], [2, 20, 7], [3, 2, 20, 7], [19, 3, 2, 20], [7, 4, 1, 20], [7, 1, 20],
  [7, 3, 1, 20], [19, 3, 2, 1, 20], [4, 5, 21, 2], [5, 21, 2], [3, 5, 21, 2], [19, 3, 1, 20],
  [4, 20, 8, 7], [20, 8, 7], [3, 20, 8, 7], [19, 3, 20, 8], [2, 20, 8, 7], [14, 2, 20, 7],
  [14, 3, 2, 20, 7], [13, 2, 20, 7], [19, 8, 2, 1, 20], [8, 7, 1, 20], [7, 5, 21, 3],
  [14, 7, 1, 20], [8, 5, 21, 2], [19, 8, 1, 20], [4, 5, 21, 3, 2], [5, 21, 3, 2], [9, 21, 2, 10],
  [19, 23], [20, 7, 11], [19, 23, 3], [8, 19, 16, 23], [19, 16, 23], [8, 19, 16, 23, 3],
  [19, 16, 23, 3], [9, 21, 10], [19, 23, 2], [9, 21, 1, 10], [19, 23, 3, 2], [9, 21, 10, 2],
  [19, 23, 21], [9, 21, 10, 3, 2], [19, 23, 21, 3], [21, 2, 10], [19, 23, 8], [20, 2, 1, 10],
  [19, 23, 5, 3], [21, 10, 8, 2], [16, 23, 8], [21, 10, 8, 3, 2], [16, 23, 5, 3], [19, 23, 8, 2],
  [21, 10], [19, 23, 8, 3, 2], [21, 1, 10], [16, 23, 8, 2], [21, 10, 2], [16, 23, 8, 3, 2],
  [21, 10, 3, 2], [3, 19, 15, 23], [19, 15, 23], [20, 11, 7, 3], [15, 23, 3], [3, 19, 1, 15, 23],
  [19, 1, 15, 23], [1, 20, 11, 7, 3], [1, 15, 23, 3], [11, 10, 9, 7, 21], [19, 2, 15, 23],
  [2, 20, 11, 7, 3], [15, 13, 22, 3], [10, 9, 7, 21, 2], [19, 23, 7, 1, 20], [10, 7, 21, 3, 2],
  [11, 2, 15, 23], [3, 19, 15, 23, 8], [19, 15, 23, 8], [20, 11, 7, 5, 3], [15, 23, 5, 3],
  [5, 21, 10, 8, 2], [16, 15, 23, 8], [4, 5, 21, 10, 8, 2], [9, 1, 15, 23, 3], [19, 2, 15, 23, 8],
  [4, 10, 22, 15, 3], [2, 15, 23, 5, 3], [10, 22, 15, 3], [10, 8, 7, 21, 2], [10, 7, 21, 2],
  [19, 3, 10, 7, 21], [4, 10, 7, 21, 2], [4, 20, 11], [19, 23, 7], [19, 23, 7, 3], [20, 11],
  [11, 10, 4, 2, 20], [19, 7, 16, 23], [19, 7, 16, 23, 3], [9, 11, 22, 10, 2], [9, 21, 20, 10],
  [19, 23, 5, 2], [19, 23, 7, 3, 2], [1, 20, 11], [9, 7, 21, 10, 2], [19, 23, 7, 21],
  [19, 23, 7, 21, 3], [14, 7, 21, 10, 2], [4, 20, 1, 10], [19, 23, 8, 7], [19, 23, 7, 5, 3],
  [20, 1, 10], [7, 21, 10, 8, 2], [16, 13, 22, 8], [16, 13, 22, 8, 2], [11, 22, 10, 2],
  [19, 23, 8, 5, 2], [21, 20, 10], [2, 20, 1, 10], [19, 23, 5, 3, 2], [16, 23, 22, 8, 2],
  [7, 21, 10, 2], [7, 21, 10, 3, 2], [13, 7, 21, 10, 2], [4, 20, 15, 3], [19, 23, 20],
  [15, 23, 7, 3], [20, 15, 3], [11, 4, 2, 20, 7], [19, 23, 2, 1, 20], [7, 1, 15, 23, 3],
  [11, 2, 20, 7], [4, 2, 20, 15, 3], [19, 23, 2, 20], [15, 23, 22, 7, 3], [2, 20, 15, 3],
  [9, 5, 21, 10, 2], [19, 23, 1, 20], [10, 3, 5, 21, 2], [11, 5, 21, 2], [4, 20, 15, 5, 3],
  [19, 23, 20, 8], [15, 23, 7, 5, 3], [20, 15, 5, 3], [10, 7, 21, 8, 2], [10, 7, 16, 23],
  [19, 8, 11, 2, 20], [9, 11, 2, 20, 7], [19, 23, 2, 20, 8], [14, 2, 20, 15, 3], [2, 20, 15, 5, 3],
  [17, 10, 3, 20, 2], [5, 16, 23, 8, 2], [5, 21, 10, 2], [4, 5, 21, 10, 2], [19, 8, 1, 20, 3],
  [23, 8, 16, 2, 10], [23], [20, 15, 7, 11], [23, 3], [9, 21, 8, 2], [16, 23], [9, 21, 8, 3, 2],
  [16, 23, 3], [9, 21, 8], [23, 21], [9, 21, 5, 3], [23, 21, 3], [23, 8, 16, 10], [23, 2],
  [23, 8, 16, 1, 10], [23, 3, 2], [21, 16, 2, 10], [23, 8], [20, 15, 2, 1, 10], [23, 5, 3],
  [21, 8, 2], [9, 16, 23], [21, 8, 3, 2], [9, 16, 23, 3], [9, 23, 21], [21, 8], [9, 23, 21, 3],
  [21, 5, 3], [23, 8, 2], [21, 16, 10], [23, 8, 3, 2], [21, 16, 1, 10], [4, 20, 7, 3], [15, 23],
  [20, 7, 3], [4, 15, 23], [9, 5, 21, 8, 2], [1, 15, 23], [1, 20, 7, 3], [4, 1, 15, 23],
  [10, 9, 7, 21], [23, 7, 1, 20], [7, 1, 20, 3], [4, 23, 7, 1, 20], [4, 2, 20, 7, 3], [2, 15, 23],
  [2, 20, 7, 3], [4, 2, 15, 23], [4, 20, 7, 5, 3], [15, 23, 8], [20, 7, 5, 3], [4, 15, 23, 8],
  [5, 21, 8, 2], [9, 1, 15, 23], [4, 5, 21, 8, 2], [5, 16, 23, 3], [9, 23, 7, 1, 20], [10, 7, 21],
  [3, 10, 7, 21], [4, 10, 7, 21], [2, 15, 23, 8], [4, 5, 2, 20, 3], [4, 2, 15, 23, 8],
  [5, 2, 20, 3], [4, 20, 3], [23, 20], [4, 23, 20], [20, 3], [11, 4, 2, 20], [23, 2, 1, 20],
  [4, 23, 2, 1, 20], [11, 2, 20], [4, 1, 20, 3], [23, 1, 20], [4, 23, 1, 20], [1, 20, 3],
  [4, 2, 20, 3], [23, 2, 20], [4, 23, 2, 20], [2, 20, 3], [4, 20, 5, 3], [23, 20, 8],
  [4, 23, 20, 8], [20, 5, 3], [11, 2, 20, 8], [9, 23, 2, 1, 20], [8, 11, 2, 20], [9, 11, 2, 20],
  [9, 23, 1, 20], [21, 20, 8], [9, 1, 20, 3], [8, 1, 20, 3], [23, 2, 20, 8], [14, 2, 20, 3],
  [2, 20, 5, 3], [14, 23, 2, 20], [23, 3, 15, 11], [23, 7], [23, 7, 3], [20, 15, 11],
  [9, 7, 21, 8, 2], [7, 16, 23], [7, 16, 23, 3], [23, 14, 7, 21, 2], [9, 7, 21, 8], [23, 7, 21],
  [23, 7, 21, 3], [14, 7, 21, 8], [23, 8, 16, 15, 10], [23, 5, 2], [23, 7, 3, 2], [23, 1, 15, 11],
  [23, 3, 15, 1, 10], [23, 8, 7], [23, 7, 5, 3], [20, 15, 1, 10], [7, 21, 8, 2], [9, 7, 16, 23],
  [9, 7, 16, 23, 3], [1, 7, 21, 8], [9, 23, 7, 21], [7, 21, 8], [7, 21, 5, 3], [14, 23, 7, 21],
  [23, 8, 5, 2], [23, 16, 15, 10], [23, 2, 15, 1, 10], [23, 5, 3, 2], [9, 21, 3, 15], [14, 22],
  [7, 14, 11, 22], [14, 11, 22], [20, 8, 16], [14, 22, 2], [7, 14, 11, 22, 2], [14, 11, 22, 2],
  [9, 21, 15], [14, 22, 3], [9, 21, 15, 3], [14, 22, 21], [9, 21, 1, 15], [14, 22, 3, 2],
  [9, 21, 15, 3, 2], [14, 22, 21, 2], [2, 14, 10, 22], [14, 10, 22], [2, 14, 1, 10, 22],
  [14, 1, 10, 22], [20, 10, 8, 2], [10, 22, 2], [1, 20, 10, 8, 2], [1, 10, 22, 2],
  [16, 15, 9, 8, 21], [14, 3, 10, 22], [15, 9, 8, 21, 3], [14, 22, 8, 1, 20], [3, 20, 10, 8, 2],
  [3, 10, 22, 2], [15, 8, 21, 3, 2], [16, 3, 10, 22], [21, 3, 15], [14, 22, 7], [21, 11, 7, 3],
  [11, 22, 7], [20, 3, 1, 15], [14, 22, 5, 2], [21, 10, 7, 3, 2], [11, 22, 5, 2], [14, 22, 7, 3],
  [21, 15], [11, 22, 7, 3], [21, 15, 3], [14, 22, 7, 3, 2], [21, 1, 15], [11, 22, 7, 3, 2],
  [21, 15, 3, 2], [2, 14, 10, 22, 7], [14, 10, 22, 7], [5, 21, 11, 7, 3], [11, 10, 22, 7],
  [20, 10, 8, 5, 2], [10, 22, 5, 2], [9, 1, 20, 10, 8, 2], [9, 1, 10, 22, 2], [14, 3, 10, 22, 7],
  [4, 15, 23, 10, 2], [15, 8, 7, 21, 3], [15, 8, 21, 3], [3, 10, 22, 5, 2], [15, 23, 10, 2],
  [14, 2, 15, 8, 21], [4, 15, 8, 21, 3], [4, 20, 16], [14, 22, 8], [16, 15, 4, 3, 20],
  [14, 8, 11, 22], [14, 22, 8, 2], [20, 16], [14, 8, 11, 22, 2], [9, 16, 23, 15, 3],
  [9, 21, 20, 15], [14, 22, 5, 3], [9, 8, 21, 15, 3], [14, 22, 8, 21], [14, 22, 8, 3, 2],
  [1, 20, 16], [14, 22, 8, 21, 2], [19, 8, 21, 15, 3], [4, 20, 10, 2], [14, 22, 20],
  [16, 4, 3, 20, 8], [14, 22, 3, 1, 20], [10, 22, 8, 2], [20, 10, 2], [8, 1, 10, 22, 2],
  [16, 3, 20, 8], [4, 3, 20, 10, 2], [14, 22, 3, 20], [4, 1, 20, 10, 2], [14, 22, 1, 20],
  [3, 10, 22, 8, 2], [3, 20, 10, 2], [1, 10, 22, 8, 2], [1, 20, 10, 2], [4, 20, 1, 15],
  [14, 22, 8, 7], [8, 21, 11, 7, 3], [8, 11, 22, 7], [14, 22, 8, 5, 2], [20, 1, 15],
  [8, 11, 22, 5, 2], [16, 23, 15, 3], [14, 22, 7, 5, 3], [21, 20, 15], [8, 11, 22, 7, 3],
  [8, 21, 15, 3], [3, 20, 1, 15], [14, 22, 5, 3, 2], [8, 21, 15, 3, 2], [23, 11, 22, 5, 2],
  [4, 20, 10, 5, 2], [14, 22, 20, 7], [15, 8, 21, 7, 3], [15, 8, 11, 22], [10, 22, 8, 5, 2],
  [20, 10, 5, 2], [14, 7, 16, 3, 20], [9, 16, 3, 20, 8], [14, 22, 3, 20, 7], [19, 3, 20, 10, 2],
  [5, 11, 22, 7, 3], [5, 21, 15, 3], [3, 20, 10, 5, 2], [23, 10, 22, 5, 2], [9, 1, 20, 10, 2],
  [14, 7, 1, 20, 2], [22, 8, 16, 2, 10], [22], [9, 21, 7, 3], [11, 22], [20, 8, 16, 10], [22, 2],
  [9, 21, 7, 3, 2], [11, 22, 2], [9, 21, 7], [22, 21], [22, 15, 7, 11], [22, 3], [9, 21, 5, 2],
  [22, 21, 2], [22, 8, 16, 1, 10], [22, 3, 2], [4, 20, 8, 2], [10, 22], [4, 1, 20, 8, 2],
  [1, 10, 22], [20, 8, 2], [4, 10, 22], [1, 20, 8, 2], [4, 1, 10, 22], [15, 9, 8, 21],
  [22, 8, 1, 20], [4, 3, 20, 8, 2], [3, 10, 22], [8, 1, 20, 2], [4, 22, 8, 1, 20], [3, 20, 8, 2],
  [4, 3, 10, 22], [21, 3, 15, 11], [22, 7], [21, 7, 3], [9, 11, 22], [20, 8, 16, 15, 10],
  [22, 5, 2], [21, 7, 3, 2], [9, 11, 22, 2], [9, 22, 21], [21, 7], [22, 7, 3], [21, 15, 11],
  [9, 22, 21, 2], [21, 5, 2], [22, 7, 3, 2], [21, 1, 15, 11], [4, 20, 8, 5, 2], [10, 22, 7],
  [5, 21, 7, 3], [9, 1, 10, 22], [20, 8, 5, 2], [4, 10, 22, 7], [9, 1, 20, 8, 2], [5, 11, 22, 2],
  [9, 22, 8, 1, 20], [15, 8, 21], [3, 10, 22, 7], [4, 5, 3, 20, 2], [2, 15, 8, 21], [4, 15, 8, 21],
  [4, 3, 10, 22, 7], [5, 3, 20, 2], [4, 20, 2], [22, 20], [16, 4, 3, 20], [22, 3, 1, 20],
  [4, 22, 20], [20, 2], [4, 22, 3, 1, 20], [16, 3, 20], [4, 1, 20, 2], [22, 1, 20], [4, 3, 20, 2],
  [22, 3, 20], [4, 22, 1, 20], [1, 20, 2], [4, 22, 3, 20], [3, 20, 2], [22, 16, 2, 10], [22, 8],
  [9, 8, 21, 7, 3], [8, 11, 22], [22, 8, 2], [20, 16, 10], [8, 11, 22, 2], [22, 19, 8, 21, 3],
  [9, 8, 21, 7], [22, 8, 21], [22, 15, 2, 1, 10], [22, 5, 3], [22, 8, 21, 2], [19, 8, 21, 7],
  [22, 8, 3, 2], [22, 16, 1, 10], [4, 20, 5, 2], [22, 20, 7], [16, 3, 20, 7], [9, 22, 3, 1, 20],
  [4, 22, 20, 7], [20, 5, 2], [7, 16, 3, 20], [9, 16, 3, 20], [9, 22, 1, 20], [21, 20, 7],
  [22, 3, 20, 7], [19, 3, 20, 2], [9, 1, 20, 2], [7, 1, 20, 2], [3, 20, 5, 2], [19, 22, 3, 20],
  [22, 3, 15, 1, 10], [22, 8, 7], [8, 21, 7, 3], [9, 8, 11, 22], [22, 8, 5, 2], [20, 16, 15, 10],
  [9, 8, 11, 22, 2], [1, 8, 21, 7], [9, 22, 8, 21], [8, 21, 7], [22, 7, 5, 3], [22, 15, 1, 10],
  [8, 21, 5, 2], [19, 22, 8, 21], [22, 2, 15, 1, 10], [22, 5, 3, 2], [9, 21, 17, 2, 10],
  [14, 13, 22], [7, 14, 11, 22, 8], [14, 13, 11, 22], [8, 19, 16, 23, 7], [16, 14, 13, 22],
  [20, 17, 7, 11], [14, 13, 22, 2], [9, 21, 15, 10], [19, 23, 22, 2], [9, 21, 15, 5, 3],
  [14, 13, 22, 21], [9, 21, 10, 5, 2], [19, 13, 22, 21], [9, 21, 17, 1, 10], [14, 23, 22, 2],
  [2, 14, 10, 22, 3], [14, 13, 10, 22], [7, 14, 11, 22, 20], [14, 8, 11, 22, 20],
  [21, 20, 10, 8, 2], [16, 13, 10, 22], [20, 10, 8, 3, 2], [13, 10, 22, 2], [19, 23, 20, 8, 2],
  [14, 10, 22, 3], [15, 9, 23, 21, 3], [14, 10, 22, 21], [16, 23, 20, 8, 2], [10, 22, 21, 2],
  [15, 23, 8, 3, 2], [10, 22, 3, 2], [3, 19, 15, 23, 2], [15, 14, 13, 22], [21, 20, 11, 7, 3],
  [15, 13, 11, 22], [8, 19, 16, 23, 20], [14, 7, 16, 23, 20], [20, 10, 7, 3, 2], [15, 13, 22, 2],
  [14, 22, 20, 7, 3], [19, 15, 23, 2], [11, 22, 20, 7, 3], [15, 23, 21, 3], [10, 9, 22, 21, 2],
  [19, 15, 23, 21], [10, 22, 7, 3, 2], [15, 23, 3, 2], [21, 17, 2, 10], [14, 13, 22, 7],
  [21, 11, 7, 5, 3], [13, 11, 22, 7], [21, 10, 8, 5, 2], [16, 13, 22, 7], [20, 17, 2, 1, 10],
  [14, 13, 22, 5, 2], [19, 17, 23, 8, 2], [21, 15, 10], [13, 11, 22, 7, 3], [21, 15, 5, 3],
  [17, 16, 23, 8, 2], [21, 10, 5, 2], [14, 17, 23, 8, 2], [21, 17, 1, 10], [4, 20, 16, 11],
  [19, 23, 22, 7], [19, 23, 21, 7, 3], [14, 11, 22, 8], [14, 22, 21, 8, 2], [19, 16, 23, 7],
  [14, 13, 22, 8, 2], [20, 16, 11], [9, 21, 20, 15, 10], [19, 23, 22, 5, 2], [9, 11, 8, 21, 7],
  [14, 22, 21, 8], [9, 16, 7, 21, 8], [19, 23, 21, 7], [14, 23, 22, 8, 2], [1, 20, 16, 11],
  [4, 20, 10, 3, 2], [14, 13, 22, 20], [16, 4, 23, 20, 8], [14, 11, 22, 20], [10, 22, 21, 8, 2],
  [16, 23, 20, 8], [13, 10, 22, 8, 2], [20, 10, 3, 2], [4, 10, 3, 20, 2], [14, 22, 20, 3],
  [4, 21, 20, 10, 2], [14, 13, 22, 1, 20], [10, 22, 8, 21, 2], [21, 20, 10, 2], [10, 22, 8, 3, 2],
  [10, 3, 20, 2], [4, 20, 15, 3, 2], [19, 13, 22, 20], [15, 23, 21, 7, 3], [11, 22, 20, 7],
  [11, 4, 22, 20, 7], [19, 16, 23, 20], [10, 7, 13, 22, 2], [20, 15, 3, 2], [4, 15, 2, 20, 3],
  [19, 23, 20, 2], [15, 23, 7, 21, 3], [21, 20, 15, 3], [9, 21, 20, 10, 2], [19, 13, 22, 1, 20],
  [15, 23, 7, 3, 2], [15, 2, 20, 3], [4, 20, 17, 1, 10], [14, 23, 22, 7], [16, 23, 7, 5, 3],
  [11, 22, 8, 7], [11, 22, 8, 5, 2], [16, 23, 8, 7], [19, 13, 22, 8, 2], [20, 17, 1, 10],
  [19, 23, 22, 8, 2], [21, 20, 15, 10], [11, 22, 7, 5, 3], [11, 8, 21, 7], [16, 23, 8, 5, 2],
  [16, 7, 21, 8], [2, 20, 17, 1, 10], [14, 23, 22, 5, 2], [9, 21, 3, 15, 1, 10], [13, 22],
  [9, 21, 7, 5, 3], [13, 11, 22], [9, 21, 8, 5, 2], [16, 13, 22], [20, 8, 16, 1, 10], [13, 22, 2],
  [9, 21, 8, 7], [13, 22, 21], [9, 21, 15, 1, 10], [13, 22, 3], [9, 21, 16, 15, 10], [23, 22, 2],
  [9, 21, 5, 3, 2], [13, 22, 21, 2], [4, 20, 8, 3, 2], [13, 10, 22], [4, 21, 20, 8, 2],
  [8, 11, 22, 20], [21, 20, 8, 2], [8, 11, 4, 22, 20], [20, 8, 3, 2], [13, 4, 10, 22],
  [15, 9, 23, 21], [10, 22, 21], [4, 23, 20, 8, 2], [10, 22, 3], [23, 20, 8, 2], [4, 10, 22, 3],
  [8, 1, 20, 3, 2], [4, 10, 22, 21], [4, 20, 7, 3, 2], [15, 13, 22], [21, 20, 7, 3],
  [9, 8, 11, 22, 20], [9, 21, 20, 8, 2], [7, 16, 23, 20], [20, 7, 3, 2], [4, 15, 13, 22],
  [10, 9, 22, 21], [15, 23, 21], [22, 20, 7, 3], [4, 15, 23, 2], [4, 22, 20, 7, 3], [15, 23, 2],
  [7, 1, 20, 3, 2], [4, 15, 23, 21], [21, 3, 15, 1, 10], [13, 22, 7], [21, 7, 5, 3],
  [13, 9, 11, 22], [21, 8, 5, 2], [9, 16, 13, 22], [20, 2, 15, 1, 10], [13, 22, 5, 2],
  [13, 9, 22, 21], [21, 8, 7], [13, 22, 7, 3], [21, 15, 1, 10], [17, 23, 8, 2], [21, 16, 15, 10],
  [13, 9, 22, 21, 2], [21, 5, 3, 2], [4, 20, 3, 2], [13, 22, 20], [16, 4, 23, 20], [11, 22, 20],
  [11, 4, 22, 20], [16, 23, 20], [13, 4, 22, 20], [20, 3, 2], [4, 1, 20, 3, 2], [13, 22, 1, 20],
  [4, 23, 20, 2], [22, 20, 3], [4, 22, 20, 3], [23, 20, 2], [13, 4, 22, 1, 20], [1, 20, 3, 2],
  [4, 20, 16, 1, 10], [13, 22, 8], [9, 23, 21, 7, 3], [11, 22, 8], [22, 21, 8, 2], [9, 16, 23, 7],
  [13, 22, 8, 2], [20, 16, 1, 10], [9, 23, 21, 7], [22, 21, 8], [7, 21, 15, 1, 10], [13, 22, 5, 3],
  [23, 22, 8, 2], [21, 20, 16, 10], [4, 22, 21, 8], [20, 19, 8, 21, 3], [4, 20, 1, 15, 11],
  [23, 22, 7], [23, 21, 7, 3], [9, 11, 22, 8], [9, 22, 21, 8, 2], [16, 23, 7], [7, 13, 22, 2],
  [20, 1, 15, 11], [9, 22, 21, 8], [23, 21, 7], [23, 22, 7, 3], [21, 20, 15, 11],
  [8, 21, 16, 15, 10], [23, 22, 5, 2], [4, 23, 21, 7], [20, 14, 7, 21, 2], [4, 20, 5, 3, 2],
  [13, 22, 20, 7], [1, 9, 23, 20, 2], [9, 11, 22, 20], [7, 21, 20, 8, 2], [9, 16, 23, 20],
  [13, 4, 22, 20, 7], [20, 5, 3, 2], [13, 9, 22, 1, 20], [21, 20, 8, 7], [9, 22, 20, 3],
  [19, 10, 3, 20, 2], [9, 23, 20, 2], [15, 14, 2, 20, 3], [9, 1, 20, 3, 2], [13, 7, 1, 20, 2]]

@[expose] def actC (t c : ℕ) : ℕ :=
  (List.finRange 10).foldl
    (fun acc (l : Fin 10) => if c.testBit l then acc ^^^ l52Col.getD (10 * t + l) 0 else acc) 0

@[expose] def applyC (l : List ℕ) (c : ℕ) : ℕ := l.foldr actC c

@[expose] def l52BaseC (b : Bool) : ℕ := if b then 1 else 129

end CFSG.Quasithin.H13.Orbit
