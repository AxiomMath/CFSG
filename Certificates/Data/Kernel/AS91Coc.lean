module

public import CFSG.Quasithin.H13.AS91Sec8V1CocData
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.KS.AS91Coc

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
open CFSG.Quasithin.H13.AS91.M24G

@[expose] noncomputable def PA : Nat := 813304421967572652703672355640554894

@[expose] noncomputable def PAi : Nat := 254635182913684525743004454421548594

@[expose] noncomputable def PB : Nat := 3977357184663146755246157689470380

@[expose] noncomputable def PBi : Nat := 426226701517939227225388813867767447

@[expose] noncomputable def permColsK (P : Nat) : List Nat :=
  (List.range 24).map fun j => 2 ^ pg 5 (mask 5) P j

@[expose] noncomputable def act11K (P m : Nat) : Nat :=
  actM ccECols (actM (permColsK P) (actM liftECols m))

@[expose] noncomputable def invLetK (l : CocL) : Nat := CocL.rec PAi PA PBi PB l

@[expose] noncomputable def valK (x y : Nat) (l : CocL) : Nat :=
  CocL.rec x (act11K PA x) y (act11K PB y) l

@[expose] noncomputable def foldK (x y : Nat) (w : List CocL) : Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (pidn 24 5, 0)
    (fun l _ p => (pcomp 24 5 (mask 5) p.1 (invLetK l), Nat.xor (act11K p.1 (valK x y l)) p.2)) w

@[expose] noncomputable def imgLetK (l : CocL) : Nat := CocL.rec PA PAi PB PBi l

@[expose] noncomputable def relK (w : List CocL) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 24 5) (fun l _ acc => pcomp 24 5 (mask 5) (imgLetK l) acc) w

@[expose] noncomputable def relOKK : Bool :=
  cocRelWords.all fun w => (List.range 24).all fun j => pg 5 (mask 5) (relK w) j == j

@[expose] noncomputable def cocWalk (g : Nat → Nat → Bool) (L : List Nat) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih i => g i t && ih (Nat.succ i)) L i

@[expose] def cocMA : List Nat := [1024, 1024, 1536, 1567, 0, 1567, 512, 1567, 512, 512, 1024]

@[expose] def cocMW : List (List Nat) :=
  [[1087, 274, 0, 1087, 274, 0, 1087, 0, 0, 1087, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [799, 1951, 864, 0, 2016, 1152, 1279, 1152, 1951, 864, 799],
   [406, 212, 486, 646, 546, 0, 1439, 0, 1791, 864, 1440],
   [1568, 1197, 1917, 770, 1778, 1952, 1568, 1952, 607, 1151, 1535],
   [1052, 1162, 860, 60, 1014, 448, 1791, 448, 1439, 864, 736],
   [342, 76, 2007, 520, 1221, 1279, 735, 1279, 1792, 1503, 1184],
   [970, 1790, 22, 585, 1899, 0, 607, 0, 0, 607, 0],
   [960, 1567, 960, 863, 1344, 1503, 863, 1503, 960, 159, 1503],
   [725, 1128, 1066, 1845, 1442, 1024, 256, 1024, 543, 799, 767],
   [1789, 486, 1607, 120, 292, 768, 288, 768, 1823, 1599, 639],
   [827, 1983, 1111, 1879, 1924, 1119, 1279, 1119, 2047, 768, 1631],
   [76, 306, 485, 762, 609, 352, 512, 352, 287, 799, 95],
   [1311, 1482, 2024, 1032, 821, 383, 1151, 383, 1951, 992, 863],
   [1865, 1495, 1381, 901, 1150, 1984, 1663, 1984, 159, 1760, 1503],
   [346, 1861, 794, 762, 2047, 1536, 1280, 1536, 1248, 480, 1920],
   [183, 882, 1415, 1528, 954, 1280, 256, 1280, 383, 127, 1983],
   [2038, 1640, 985, 1382, 1825, 160, 2016, 160, 351, 1727, 800],
   [1186, 1164, 213, 1770, 1553, 1503, 1279, 1503, 704, 1599, 992],
   [85, 1785, 1588, 1652, 1772, 927, 639, 927, 575, 64, 960],
   [767, 1500, 1715, 204, 348, 1664, 1152, 1664, 767, 1663, 1760],
   [818, 1057, 1218, 1186, 1907, 1631, 64, 1631, 32, 96, 160],
   [1303, 227, 576, 640, 1332, 447, 288, 447, 480, 192, 863],
   [1403, 14, 1875, 563, 21, 160, 1439, 160, 255, 1376, 1472],
   [158, 282, 698, 954, 132, 32, 31, 32, 287, 256, 1439]]

@[expose] noncomputable def mwChunk (c : Nat) : Bool :=
  (List.range 5).all fun j =>
    matOf 11 (fun y => (foldK 0 y (cocRelWords.getD (5 * c + j) [])).2) == cocMW.getD (5 * c + j) []

@[expose] noncomputable def cocGA (x t : Nat) : Bool :=
  !(actM cocMA x == 0) || (act11K PAi t ^^^ t) == x

@[expose] noncomputable def cocGB (y t : Nat) : Bool :=
  !(cocMW.all fun M => actM M y == 0) ||
    ((act11K PAi (t % 2048) ^^^ t % 2048) ^^^ (if t / 4096 % 2 = 1 then cocDBetaA else 0) == 0 &&
      (act11K PBi (t % 2048) ^^^ t % 2048) ^^^ (if t / 2048 % 2 = 1 then cocZeta else 0) ^^^
        (if t / 4096 % 2 = 1 then cocDBetaB else 0) == y)

@[expose] noncomputable def letOK (a : Array Nat) (P : Nat) : Bool :=
  (List.range 24).all fun j => a[j]! == pg 5 (mask 5) P j && Nat.blt (pg 5 (mask 5) P j) 24

end CFSG.KS.AS91Coc

end
