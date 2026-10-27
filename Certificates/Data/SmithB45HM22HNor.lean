module

public import CFSG.Quasithin.Background.SmithB45HM22Comp
public import CFSG.Quasithin.Background.SmithB45HM22Chk
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour

@[expose] def hAW : List ℤ := [-1, -2, -1, -2, 1, 2, 1, 2]

@[expose] def hBW : List ℤ := [-1, -2, -1, -2, -2, -2, -1, 2, 1, 2, 2, 2, 1, 2, 1]

@[expose] def hnor3a : PSpin where
  terms := [([false], 1), ([false, false], 1)]
  Q :=
    [(3, 1),
     (1, 0),
     (4, 0)]
  Qi :=
    [(2, 0),
     (3, 2),
     (4, 0)]
  R :=
    [(0, 0),
     (2, 0),
     (6, 0)]
  spin :=
    [(0, true), (1, false)]
  Si :=
    [(7, 6),
     (0, 7),
     (5, 3)]
  w := (5, 2)
  dual :=
    [(0, true), (1, false)]
  Ti :=
    [(7, 2),
     (1, 3),
     (2, 4)]

@[expose] def hnorCheck3a : Bool :=
  (hnor3a.toSpin 3).check (PM.unpack 3 3 (blk3a hAW)) (PM.unpack 3 3 (blk3a hBW))

@[expose] def hnor3b : PSpin where
  terms := [([false], 1), ([false, false], 1)]
  Q :=
    [(6, 1),
     (1, 0),
     (2, 0)]
  Qi :=
    [(2, 0),
     (4, 0),
     (5, 2)]
  R :=
    [(0, 0),
     (6, 0),
     (4, 0)]
  spin :=
    [(0, true), (1, true)]
  Si :=
    [(7, 5),
     (0, 6),
     (4, 4)]
  w := (7, 3)
  dual :=
    [(0, true), (1, false)]
  Ti :=
    [(1, 7),
     (4, 1),
     (3, 0)]

@[expose] def hnorCheck3b : Bool :=
  (hnor3b.toSpin 3).check (PM.unpack 3 3 (blk3b hAW)) (PM.unpack 3 3 (blk3b hBW))

@[expose] def hnor9 : PSpin where
  terms := [([false], 1), ([true, true], ω)]
  Q :=
    [(365, 5),
     (1, 0),
     (2, 0),
     (4, 0),
     (8, 0),
     (16, 0),
     (32, 0),
     (64, 0),
     (128, 0)]
  Qi :=
    [(2, 0),
     (4, 0),
     (8, 0),
     (16, 0),
     (32, 0),
     (64, 0),
     (128, 0),
     (256, 0),
     (219, 10)]
  R :=
    [(0, 0),
     (294, 148),
     (6, 432),
     (302, 470),
     (232, 216),
     (292, 470),
     (112, 226),
     (98, 474),
     (118, 264)]
  spin :=
    [(0, false), (0, true), (1, false), (1, true), (2, false), (3, true), (4, false), (5, false)]
  Si :=
    [(468, 322),
     (406, 278),
     (468, 320),
     (49, 376),
     (40, 317),
     (48, 368),
     (322, 312),
     (284, 318),
     (320, 304)]
  w := (65, 0)
  dual :=
    [(0, false), (0, true), (1, false), (1, true), (2, false), (3, true), (4, false), (6, false)]
  Ti :=
    [(41, 12),
     (16, 2),
     (8, 40),
     (54, 48),
     (32, 32),
     (511, 511),
     (24, 40),
     (365, 511),
     (73, 73)]

@[expose] def hnorCheck9 : Bool :=
  (hnor9.toSpin 9).check (PM.unpack 9 9 (blk9 hAW)) (PM.unpack 9 9 (blk9 hBW))

@[expose] def hnor24a : PSpin where
  terms := [([false], 1), ([true], ω), ([false, false], ω)]
  Q :=
    [(10405314, 5587504),
     (1, 0),
     (2, 0),
     (4, 0),
     (8, 0),
     (16, 0),
     (32, 0),
     (64, 0),
     (128, 0),
     (256, 0),
     (512, 0),
     (1024, 0),
     (2048, 0),
     (4096, 0),
     (8192, 0),
     (16384, 0),
     (32768, 0),
     (65536, 0),
     (131072, 0),
     (262144, 0),
     (524288, 0),
     (1048576, 0),
     (2097152, 0),
     (4194304, 0)]
  Qi :=
    [(2, 0),
     (4, 0),
     (8, 0),
     (16, 0),
     (32, 0),
     (64, 0),
     (128, 0),
     (256, 0),
     (512, 0),
     (1024, 0),
     (2048, 0),
     (4096, 0),
     (8192, 0),
     (16384, 0),
     (32768, 0),
     (65536, 0),
     (131072, 0),
     (262144, 0),
     (524288, 0),
     (1048576, 0),
     (2097152, 0),
     (4194304, 0),
     (8388608, 0),
     (4033413, 11175008)]
  R :=
    [(0, 0),
     (3304730, 3489718),
     (1229712, 10881622),
     (3857150, 9789632),
     (10702256, 14050906),
     (1665566, 9794868),
     (12128746, 6204314),
     (4518272, 14203912),
     (12337030, 10548900),
     (38136, 15253884),
     (10110554, 14120494),
     (14387088, 9839122),
     (3876956, 2199644),
     (13828108, 16771594),
     (13908188, 9823986),
     (6503500, 2786612),
     (3391426, 13512616),
     (9380560, 16364760),
     (16357330, 2965032),
     (1643030, 11229852),
     (3551898, 11526504),
     (5538798, 14839630),
     (12221756, 11834196),
     (16506310, 2284170)]
  spin :=
    [(0, false), (0, true), (1, true), (2, true), (3, false), (3, true), (4, false), (4, true),
     (5, false), (5, true), (6, false), (6, true), (7, false), (7, true), (8, false), (9, true),
     (10, false), (10, true), (11, false), (11, true), (12, false), (13, true), (14, false)]
  Si :=
    [(10126372, 6031923),
     (1578941, 16539283),
     (11675775, 7089796),
     (12660681, 12944673),
     (13896806, 9886580),
     (7481282, 3652606),
     (7394842, 6822106),
     (3515822, 9837106),
     (3047119, 853312),
     (16026030, 7754710),
     (14863800, 3834344),
     (10958720, 9533514),
     (12985072, 8910031),
     (8573268, 12042245),
     (1814271, 4343869),
     (2718631, 6965506),
     (5364067, 13871576),
     (10050654, 5849567),
     (15610055, 9619566),
     (3447273, 8408245),
     (1950636, 15026359),
     (3791090, 12708739),
     (12798366, 6527458),
     (11534201, 13234366)]
  w := (14225713, 4344275)
  dual :=
    [(0, false), (0, true), (1, true), (2, true), (3, false), (3, true), (4, false), (4, true),
     (5, false), (5, true), (6, false), (6, true), (7, false), (7, true), (8, false), (9, true),
     (10, false), (10, true), (11, false), (11, true), (12, false), (13, true), (14, false)]
  Ti :=
    [(14943990, 3184801),
     (14824865, 14119052),
     (10665780, 13946463),
     (5517025, 12209626),
     (1116645, 829662),
     (1716170, 6513791),
     (7347269, 11260038),
     (16534479, 10626405),
     (15710320, 7075701),
     (10493269, 8795474),
     (8409686, 10949581),
     (3964052, 16502391),
     (9350038, 2571540),
     (1161013, 3115677),
     (14536050, 9680252),
     (8606416, 1848195),
     (7305543, 5956079),
     (14587608, 15627940),
     (14736524, 5374124),
     (8993682, 16432281),
     (12898150, 11647195),
     (8615269, 14126663),
     (11413611, 14639555),
     (10157547, 3902323)]

@[expose] def hnorCheck24a : Bool :=
  (hnor24a.toSpin 24).check (PM.unpack 24 24 (blk24a hAW)) (PM.unpack 24 24 (blk24a hBW))

@[expose] def hnor24b : PSpin where
  terms := [([false], 1), ([true], ω), ([false, false], ω)]
  Q :=
    [(13506854, 4967193),
     (1, 0),
     (2, 0),
     (4, 0),
     (8, 0),
     (16, 0),
     (32, 0),
     (64, 0),
     (128, 0),
     (256, 0),
     (512, 0),
     (1024, 0),
     (2048, 0),
     (4096, 0),
     (8192, 0),
     (16384, 0),
     (32768, 0),
     (65536, 0),
     (131072, 0),
     (262144, 0),
     (524288, 0),
     (1048576, 0),
     (2097152, 0),
     (4194304, 0)]
  Qi :=
    [(2, 0),
     (4, 0),
     (8, 0),
     (16, 0),
     (32, 0),
     (64, 0),
     (128, 0),
     (256, 0),
     (512, 0),
     (1024, 0),
     (2048, 0),
     (4096, 0),
     (8192, 0),
     (16384, 0),
     (32768, 0),
     (65536, 0),
     (131072, 0),
     (262144, 0),
     (524288, 0),
     (1048576, 0),
     (2097152, 0),
     (4194304, 0),
     (8388608, 0),
     (10236493, 9934386)]
  R :=
    [(0, 0),
     (14241186, 5472172),
     (12578044, 6951276),
     (9054022, 16193940),
     (15910262, 5621492),
     (10784640, 16724526),
     (5749810, 10252044),
     (5695300, 15813016),
     (3609350, 14783958),
     (12460302, 14382178),
     (8605046, 15859892),
     (16552832, 10317120),
     (2123848, 4040110),
     (13301640, 2625024),
     (6136940, 11210550),
     (13095414, 5101344),
     (6272, 12919778),
     (12423556, 1275916),
     (9476872, 10368460),
     (2416814, 15027348),
     (3408900, 9379280),
     (12977884, 145272),
     (16693902, 7141118),
     (5704354, 1069274)]
  spin :=
    [(0, false), (0, true), (1, true), (2, true), (3, false), (3, true), (4, false), (4, true),
     (5, false), (5, true), (6, false), (6, true), (7, false), (7, true), (8, false), (9, true),
     (10, false), (10, true), (11, false), (11, true), (12, false), (13, true), (14, false)]
  Si :=
    [(11925104, 12423146),
     (10248671, 1817115),
     (1037530, 13704310),
     (4536000, 14792450),
     (4183966, 14528053),
     (7149743, 8345493),
     (5491991, 6580323),
     (15634223, 3115007),
     (11036931, 8287359),
     (14123398, 5561337),
     (9631555, 3319812),
     (14289939, 16309420),
     (16356356, 4191641),
     (7054001, 7195745),
     (4488182, 1522136),
     (9916218, 14213133),
     (7438142, 4156527),
     (7783108, 14874397),
     (10729595, 12611230),
     (2376469, 866196),
     (15652113, 6953505),
     (5117935, 4753054),
     (7893809, 15360717),
     (5956653, 9296075)]
  w := (8442017, 6877700)
  dual :=
    [(0, false), (0, true), (1, true), (2, true), (3, false), (3, true), (4, false), (4, true),
     (5, false), (5, true), (6, false), (6, true), (7, false), (7, true), (8, false), (9, true),
     (10, false), (10, true), (11, false), (11, true), (12, false), (13, true), (14, false)]
  Ti :=
    [(1882305, 12850161),
     (11405579, 14061823),
     (16475082, 11508240),
     (13498854, 12726343),
     (12175383, 539187),
     (2221749, 13658903),
     (3255139, 15366912),
     (4297693, 8950086),
     (11795968, 12542298),
     (3356531, 3950469),
     (12927811, 15505999),
     (16466873, 901409),
     (12946448, 15347123),
     (15096847, 10449838),
     (8737785, 8171867),
     (9070491, 5139920),
     (1540100, 11242284),
     (7092570, 2465129),
     (6466002, 12354457),
     (1009832, 12565616),
     (16658876, 12204282),
     (8695655, 9301612),
     (10851759, 1893464),
     (6271065, 15339478)]

@[expose] def hnorCheck24b : Bool :=
  (hnor24b.toSpin 24).check (PM.unpack 24 24 (blk24b hAW)) (PM.unpack 24 24 (blk24b hBW))

@[expose] def hTraceCheck : Bool :=
  PM.trace 3 (blk3a (hAW ++ hBW)) != PM.trace 3 (blk3b (hAW ++ hBW)) &&
    PM.trace 24 (blk24a (hAW ++ hAW ++ hBW)) != PM.trace 24 (blk24b (hAW ++ hAW ++ hBW))

end CFSG.Quasithin.HM22
