module

public import Certificates.Data.CFSGNative.PropA.Check

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA.Data

open CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.M12Std.PropA.Native

@[expose] def tabA : Table :=
  #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5, 15, 13, 21, 12, 22, 23, 18, 19, 20, 14, 16, 17, 24,
  25, 26, 27]

@[expose] def tabB : Table :=
  #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10, 17, 20, 13, 12, 19, 15, 22, 21, 14, 16, 23, 18, 24,
  25, 26, 27]

@[expose] def tabG1 : Table :=
  #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25,
  24, 27, 26]

@[expose] def tabG2 : Table :=
  #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 25,
  26, 27, 24]

@[expose] def tabT : Table :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26,
  27, 24, 25]

@[expose] def wx0 : Word :=
  [1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2]

@[expose] def wj1 : Word :=
  [1, -2, 1, -2, 1, 2]

@[expose] def wj2 : Word :=
  [1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1]

@[expose] def wj3 : Word :=
  [1, -2, 1, -2, 1, 2]

@[expose] def wj4 : Word :=
  [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2]

@[expose] def jWords : JWords where
  a₁ := wj1
  b₁ := wj2
  a₂ := wj3
  b₂ := wj4

@[expose] def wr5 : Word :=
  [1]

@[expose] def wz6 : Word :=
  [-1, -2, -2, 1, 2]

@[expose] def wk7 : Word :=
  [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2]

@[expose] def wa8 : Word :=
  [-2, 1, 2, 2, 4, -2, 4, 2, -4, -3, -4, -3, 4, -3]

@[expose] def wb9 : Word :=
  [3, -4, 3, 4, 3, 2, 1, 3, 1, 3]

@[expose] def wz10 : Word :=
  [-1, -2, -1, 2, 1, -2, -2]

@[expose] def wk11 : Word :=
  [2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2]

@[expose] def wa12 : Word :=
  [-2, 1, -2, -3, -1, -3, -2, 4, -3, -4]

@[expose] def wb13 : Word :=
  [2, -1, -4, 2, 4, 3, 1, 2, 2, 1, -4, 2, 1, 4, 2, 4, 3, -1, -3]

@[expose] def wz14 : Word :=
  [-1, 2, 1, -2, -2]

@[expose] def wk15 : Word :=
  [1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2]

@[expose] def wa16 : Word :=
  [-2, 1, 3, 1, -2, -4, -2, -4, -2, -1, 2, -1, -2, -1]

@[expose] def wb17 : Word :=
  [1, 2, 1, -2, 1, 2, 4, 4, 2, -1, -3, -4, -1, -2, -3]

@[expose] def wz18 : Word :=
  [-2, 1, 2]

@[expose] def wk19 : Word :=
  [1]

@[expose] def wa20 : Word :=
  [-2, -2, 4, 4, 2, 4, -2, -2, 4, -2, -2, -1, 2, -1, -2, -1]

@[expose] def wb21 : Word :=
  [2, 2, 4, -2, -2, 4, 2, 4, -1, -2, -2, 4, -3, -2, 3, 1]

@[expose] def wz22 : Word :=
  [-1, -2, -1, -2, -1, 2, 1, -2, -2]

@[expose] def wk23 : Word :=
  [1, -2, 1]

@[expose] def wa24 : Word :=
  [-2, 1, -2, -4, -4, 2, -4, 2, -3, -4, 2, -3, -4, 2, -1, -3]

@[expose] def wb25 : Word :=
  [3, -4, -2, -1, -4, -4, -2, -4, 3, 2, -1, -2]

@[expose] def wz26 : Word :=
  [-1, -2, -2, 1, -2, -1, -2, -1, 2, 1, -2, -2]

@[expose] def wk27 : Word :=
  [1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2]

@[expose] def wa28 : Word :=
  [-2, 4, -2, 1, 4, -2, 1, 4]

@[expose] def wb29 : Word :=
  [3, -4, 3, 4, 3, 4, 4, -1, 4, 4, 4]

@[expose] def wz30 : Word :=
  [-2, -2, -1, -2, -1, 2, 1, -2, -2]

@[expose] def wk31 : Word :=
  [1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2]

@[expose] def wa32 : Word :=
  [-1, 4, -1, 4, 2, 2, -4, -2, -4, -2, -2, -1, -4, 2, -3, 4, 1, -2, -2, -3]

@[expose] def wb33 : Word :=
  [3, 2, 1, -4, -3, 4, 4, -2, 4, -1, -4, -2, -2, -1, -4, 2, -3, 4, 1, -3]

@[expose] def wz34 : Word :=
  [-2, 1, -2, -2, -2, -1, -2, -1, 2, 1, 2, 2]

@[expose] def wk35 : Word :=
  [-2, 1, 2, 1, 2]

@[expose] def wa36 : Word :=
  [4, -2, 1, 3, 1, -3, -2, -3, 2, -4, -1, 4, -2, -2]

@[expose] def wb37 : Word :=
  [-2, -2, -3, -2, -3, 4, 4, 2, 4, -1, -2]

@[expose] def wz38 : Word :=
  [2, 2, -1, -2, -1, 2, 1, -2, -2]

@[expose] def wk39 : Word :=
  [1, -2, 1, 2, 1, 2]

@[expose] def wa40 : Word :=
  [-2, 3, 1, -2, -2, 3, 2, -4, -1, -2, -4, -1, -2, 1, -2, 1]

@[expose] def wb41 : Word :=
  [2, 1, -4, 1, 3, -4, 1, 3, 1, -2, -4, 1, -2, -4, 1, -4, -3, 4]

@[expose] def wz42 : Word :=
  [-2, -2, 1, 2, 2, -1, -2, -1, 2, 1, -2, -2]

@[expose] def wk43 : Word :=
  [1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2]

@[expose] def wa44 : Word :=
  [-1, 2, -4, -4, 2, 4, -2, -3, 2, 2, 1, 2, 1, -2, -1, 2]

@[expose] def wb45 : Word :=
  [-1, 4, -2, -1, 4, -2, -2, 3, 2, 3, 4, 2]

@[expose] def wz46 : Word :=
  [-2, -2, 1, 2, 2]

@[expose] def wk47 : Word :=
  [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def wa48 : Word :=
  [-2, 1, 4, 2, 2, 2, -4, -2, -4, 2, 4]

@[expose] def wb49 : Word :=
  [4, -2, 4, 2, 4, -2, -2, -2, -4, 1, 4, 1]

@[expose] def wz50 : Word :=
  [-1]

@[expose] def wk51 : Word :=
  [-2, 1, 2]

@[expose] def wa52 : Word :=
  [-2, 1, 4, 2, 2, -4, 2, 4, 4, 2, -1, -4, -1, 4, -1]

@[expose] def wb53 : Word :=
  [-4, -4, -2, -4, -4, -2, 4, 1, 4, -2, -4, 1, 2, 2, -4]

@[expose] def wz54 : Word :=
  [-2, -2, -1, -2, -1, 2, 1, 2, 2]

@[expose] def wk55 : Word :=
  [-2, 1, 2, 1, -2, 1]

@[expose] def wa56 : Word :=
  [4, 2, 2, 2, 3, -2, 4, 2, -1, 2, -4, -2, -1, -1, 2, -4, -4, -3, 2, -1, -4, -3, 2, 2, -4, -3]

@[expose] def wb57 : Word :=
  [3, 2, 2, -4, 1, -2, -2, 4, 2, 4, 4, -2, -2, -4, 2, 1, -2, -2, 1]

@[expose] def wz58 : Word :=
  [2, -1, -2, -1, 2, 1, -2, -2]

@[expose] def wk59 : Word :=
  [2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2]

@[expose] def wa60 : Word :=
  [-1, -4, 2, 4, -2, -4, 2, 3, -2, -1, -4, -2, -1, -4, -2]

@[expose] def wb61 : Word :=
  [-1, -1, -4, -1, -4, 2, 2, 1, -4, 3, 2, -4, 1, 2]

@[expose] def wz62 : Word :=
  [2, 1, -2]

@[expose] def wk63 : Word :=
  [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2]

@[expose] def wa64 : Word :=
  [-4, -4, -2, -4, 2, 2, -4, -2, -2, -1, 2, -1, -2, -1]

@[expose] def wb65 : Word :=
  [2, -4, -4, 2, 2, 3, 4, 1, 2, 2, 1, 3, 1]

@[expose] def dataD : DData where
  gens := #[tabA, tabB]
  x := wx0
  jw := jWords
  rB := wr5
  g5 :=
    [{ z := wz6, k := wk7, wa := wa8, wb := wb9 },
    { z := wz10, k := wk11, wa := wa12, wb := wb13 },
    { z := wz14, k := wk15, wa := wa16, wb := wb17 },
    { z := wz18, k := wk19, wa := wa20, wb := wb21 },
    { z := wz22, k := wk23, wa := wa24, wb := wb25 },
    { z := wz26, k := wk27, wa := wa28, wb := wb29 },
    { z := wz30, k := wk31, wa := wa32, wb := wb33 },
    { z := wz34, k := wk35, wa := wa36, wb := wb37 },
    { z := wz38, k := wk39, wa := wa40, wb := wb41 },
    { z := wz42, k := wk43, wa := wa44, wb := wb45 },
    { z := wz46, k := wk47, wa := wa48, wb := wb49 },
    { z := wz50, k := wk51, wa := wa52, wb := wb53 },
    { z := wz54, k := wk55, wa := wa56, wb := wb57 },
    { z := wz58, k := wk59, wa := wa60, wb := wb61 },
    { z := wz62, k := wk63, wa := wa64, wb := wb65 }]

@[expose] def wp1_66 : Word :=
  [1]

@[expose] def wp1_67 : Word :=
  [1, 4]

@[expose] def wp1_68 : Word :=
  [1, 2, 3, -2, 3]

@[expose] def wg1_69 : Word :=
  [2, 3, -2, 1, 2, 3, -2]

@[expose] def wg1_70 : Word :=
  [2, 1, 2, 1, 3, 2, 1, 3, -2, 1, -2]

@[expose] def wc1_71 : Word :=
  [-2, -1, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1]

@[expose] def wc1_72 : Word :=
  [-1, 2, -1, 2, -1, -2, -1]

@[expose] def wc1_73 : Word :=
  [-2, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1]

@[expose] def wc1_74 : Word :=
  [2, -1]

@[expose] def wp1_75 : Word :=
  [1, 2, 3, -2, 3, 4]

@[expose] def wg1_76 : Word :=
  [2, 3, -2, 1, 2, 3, -2]

@[expose] def wg1_77 : Word :=
  [2, 1, 2, 1, 3, 2, 1, 3, -2, 1, -2]

@[expose] def wc1_78 : Word :=
  [-2, -1, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1]

@[expose] def wc1_79 : Word :=
  [2, -1, 2, -1, -2, -1]

@[expose] def wc1_80 : Word :=
  [2, 1, -2, -2]

@[expose] def wc1_81 : Word :=
  [-2, -1, 2, -1, 2, -1, -2, -1]

@[expose] def wp1_82 : Word :=
  [3]

@[expose] def wg1_83 : Word :=
  [1]

@[expose] def wg1_84 : Word :=
  [-2, 1, -2, 1, 2, 3, -2, 3, 2, 3, 2, 1, 3, -2]

@[expose] def wc1_85 : Word :=
  [-1, 2, -1, -2, -1, 2, 1]

@[expose] def wc1_86 : Word :=
  [-1, -2, 1, 2, 2, 2, 1]

@[expose] def wc1_87 : Word :=
  [2, 1, -2, -1, -2, -1, 2, 1]

@[expose] def wc1_88 : Word :=
  [2, 1, -2, -1, -2, -1, 2, 1, -2]

@[expose] def wp1_89 : Word :=
  [3, 4]

@[expose] def wg1_90 : Word :=
  [1]

@[expose] def wg1_91 : Word :=
  [-2, 1, -2, 1, 2, 3, -2, 3, 2, 3, 2, 1, 3, -2]

@[expose] def wc1_92 : Word :=
  [-1, -1, -2, -1, 2, 1, -2]

@[expose] def wc1_93 : Word :=
  [-2, 1, -2, -2, -1, -2, -1, 2, 1, -2]

@[expose] def wc1_94 : Word :=
  [-1, -2, -1, 2, 1]

@[expose] def wc1_95 : Word :=
  [-2, 1, -2, -2]

@[expose] def dataK1 : KData where
  gens := #[tabA, tabB, tabG1, tabT]
  x := wx0
  jw := jWords
  reps :=
    [{ rep := wp1_66, rdata := none }, { rep := wp1_67, rdata := none },
    { rep := wp1_68,
      rdata := some
        { gens := [wg1_69, wg1_70],
          order := 60,
          perf := [[(wc1_71, wc1_72)], [(wc1_73, wc1_74)]] } },
    { rep := wp1_75,
      rdata := some
        { gens := [wg1_76, wg1_77],
          order := 60,
          perf := [[(wc1_78, wc1_79)], [(wc1_80, wc1_81)]] } },
    { rep := wp1_82,
      rdata := some
        { gens := [wg1_83, wg1_84],
          order := 60,
          perf := [[(wc1_85, wc1_86)], [(wc1_87, wc1_88)]] } },
    { rep := wp1_89,
      rdata := some
        { gens := [wg1_90, wg1_91],
          order := 60,
          perf := [[(wc1_92, wc1_93)], [(wc1_94, wc1_95)]] } }]

@[expose] def wp2_96 : Word :=
  [1]

@[expose] def wp2_97 : Word :=
  [1, 4]

@[expose] def wp2_98 : Word :=
  [1, 2, 3, -2, -3]

@[expose] def wg2_99 : Word :=
  [2, 3, -2, 1, 2, -3, -2]

@[expose] def wg2_100 : Word :=
  [2, 1, 2, 1, 3, 2, 1, -3, -2, 1, -2]

@[expose] def wc2_101 : Word :=
  [-2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -1]

@[expose] def wc2_102 : Word :=
  [2, -1, 2, -1, -2, -1]

@[expose] def wc2_103 : Word :=
  [-2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -1]

@[expose] def wc2_104 : Word :=
  [2, -1]

@[expose] def wp2_105 : Word :=
  [1, 2, 3, -2, 3]

@[expose] def wg2_106 : Word :=
  [2, 3, -2, 1, 2, -3, -2]

@[expose] def wg2_107 : Word :=
  [2, 1, 2, 1, 3, 2, 1, -3, -2, 1, -2]

@[expose] def wc2_108 : Word :=
  [-2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -1]

@[expose] def wc2_109 : Word :=
  [2, -1, 2, -1, -2]

@[expose] def wc2_110 : Word :=
  [-2, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1]

@[expose] def wc2_111 : Word :=
  [-2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2]

@[expose] def dataK2 : KData where
  gens := #[tabA, tabB, tabG2, tabT]
  x := wx0
  jw := jWords
  reps :=
    [{ rep := wp2_96, rdata := none }, { rep := wp2_97, rdata := none },
    { rep := wp2_98,
      rdata := some
        { gens := [wg2_99, wg2_100],
          order := 60,
          perf := [[(wc2_101, wc2_102)], [(wc2_103, wc2_104)]] } },
    { rep := wp2_105,
      rdata := some
        { gens := [wg2_106, wg2_107],
          order := 60,
          perf := [[(wc2_108, wc2_109)], [(wc2_110, wc2_111)]] } }]

end CFSG.EvenSporadicStandard.M12Std.PropA.Data
