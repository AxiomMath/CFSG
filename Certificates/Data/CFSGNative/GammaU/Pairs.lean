module

public import Certificates.Data.CFSGNative.GammaU.Core

public section

set_option compiler.extract_closed false

namespace CFSG.GammaU.Native

@[expose] def invR (r : Array Nat) : Array Nat :=
  ((List.range 12).map fun j =>
    ((List.range 4096).find? fun n => appN r n == 2 ^ j).getD 0).toArray

abbrev St : Type := Nat × Array Nat × Array Nat

@[expose] def stepOf (p : Array Nat × Array Nat) (s : St) : St :=
  (appN p.1 s.1, mulR p.1 s.2.1, mulR s.2.2 p.2)

@[expose] def withInv (gs : List (Array Nat)) : List (Array Nat × Array Nat) :=
  gs.map fun g => (g, invR g)

@[expose] def orbitTr (W : List (Array Nat × Array Nat)) : List St :=
  bfsClosure (fun s : St => s.1) (W.map stepOf) 4096 [(a0, idR, idR)]
    ((∅ : Std.HashSet Nat).insert a0) []

@[expose] def okRows (r : Array Nat) : Bool := r.size == 12 && r.all (· < 4096)

@[expose] def d1Check (W : List (Array Nat × Array Nat)) (O : List St) (Lc Lg : List (Array Nat)) :
    Bool :=
  O.any fun s => W.any fun p =>
    let y := appN p.1 s.1
    match O.find? (fun t => t.1 == y) with
    | none => false
    | some t =>
      let h := mulR t.2.2 (mulR p.1 s.2.1)
      let hi := mulR s.2.2 (mulR p.2 t.2.1)
      appN h a0 == a0 && Lg.any fun l => !(Lc.contains (mulR h (mulR l hi)))

@[expose] def ptsOf (O : List St) (Lc : List (Array Nat)) (s : Array Nat) : List Nat :=
  O.filterMap fun t => if Lc.contains (mulR t.2.2 (mulR s t.2.1)) then some (appN t.2.1 a0)
    else none

@[expose] def f4Indep (x y : Nat) : Bool :=
  x != 0 && y != 0 && y != x && y != theta0N x && y != (x ^^^ theta0N x)

@[expose] def f2Indep3 (x y w : Nat) : Bool :=
  x != 0 && y != 0 && y != x && w != 0 && w != x && w != y && w != (x ^^^ y)

@[expose] def d2uCheck (O : List St) (Lc H : List (Array Nat)) : Bool :=
  Lc.any fun s => unitaryN s && !(H.contains s) &&
    let P := ptsOf O Lc s
    P.any fun x => P.any fun y => f4Indep x y

@[expose] def d2aCheck (O : List St) (Lc : List (Array Nat)) : Bool :=
  Lc.any fun s => antiN s &&
    let P := ptsOf O Lc s
    P.any fun x => P.any fun y => P.any fun w => f2Indep3 x y w

@[expose] def pairOK (p : Array Nat × Array Nat) : Bool :=
  okRows p.1 && okRows p.2 && mulR p.1 p.2 == idR && mulR p.2 p.1 == idR

@[expose] def violCheckW (W : List (Array Nat × Array Nat)) (Lc Lg H : List (Array Nat))
    (d1First : Bool) : Bool :=
  W.all pairOK && Lc.all okRows && Lg.all Lc.contains &&
    let O := orbitTr W
    if d1First then d1Check W O Lc Lg || d2uCheck O Lc H || d2aCheck O Lc
    else d2uCheck O Lc H || d2aCheck O Lc || d1Check W O Lc Lg

@[expose] def violCheck (gs Lc Lg H : List (Array Nat)) : Bool :=
  violCheckW (withInv gs) Lc Lg H false

@[expose] def enumGrp (gs : List (Array Nat)) : List (Array Nat) :=
  bfsClosure (fun x : Array Nat => x) (gs.map fun g x => mulR x g) 100000 [idR]
    ((∅ : Std.HashSet (Array Nat)).insert idR) []

@[expose] def n2Gens0 : List (Array Nat) :=
  [#[14, 3085, 3083, 7, 2464, 1424, 910, 893, 763, 455, 2054, 1030],
    #[3073, 3074, 3076, 3080, 1007, 991, 3184, 3248, 3376, 3632, 2063, 1039],
    #[1, 3074, 4, 3080, 666, 682, 64, 3248, 256, 3632, 1034, 2058],
    #[49, 50, 3124, 56, 299, 283, 3136, 3200, 304, 3584, 3012, 1988],
    #[3086, 3085, 3083, 3079, 3040, 2000, 958, 893, 763, 503, 2063, 1039],
    #[1410, 1345, 248, 52, 236, 28, 148, 84, 3643, 3380, 2863, 1820],
    #[3846, 3845, 3268, 3323, 983, 999, 3772, 3708, 3571, 563, 1551, 2575],
    #[1410, 2418, 3319, 8, 2387, 1424, 1302, 1509, 307, 512, 3493, 406],
    #[2745, 1609, 4, 3272, 2715, 1624, 1258, 1049, 256, 3827, 3178, 89],
    #[1718, 1653, 3083, 3316, 1003, 795, 3500, 3436, 763, 3335, 2788, 1751],
    #[64, 128, 256, 512, 1024, 2048, 65, 130, 260, 520, 1040, 2080],
    #[1342, 1341, 1787, 1335, 1007, 31, 4010, 3945, 3808, 3555, 3040, 2015],
    #[2, 1, 56, 52, 44, 28, 128, 64, 3584, 3328, 2816, 1792],
    #[1332, 1288, 1777, 1282, 997, 21, 3360, 540, 3178, 150, 2410, 1365]]

@[expose] def hyp10_0 : List (Array Nat) :=
  [#[3073, 3074, 4, 8, 227, 211, 3184, 3248, 256, 512, 2051, 1027],
    #[3073, 3074, 3076, 3080, 1007, 991, 3184, 3248, 3376, 3632, 2063, 1039],
    #[1, 2, 3076, 3080, 796, 812, 64, 128, 3376, 3632, 1036, 2060]]

@[expose] def resConj0 : List (Array Nat) :=
  [#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    #[4030, 124, 122, 118, 110, 94, 62, 3905, 3777, 3521, 3009, 1985],
    #[3965, 188, 185, 181, 173, 157, 61, 3970, 3778, 3522, 3010, 1986],
    #[1, 4, 2, 8, 16, 32, 64, 256, 128, 512, 1024, 2048],
    #[4030, 122, 124, 118, 110, 94, 62, 3777, 3905, 3521, 3009, 1985],
    #[3835, 314, 313, 307, 299, 283, 59, 3972, 3908, 3524, 3012, 1988],
    #[1, 56, 2, 52, 44, 28, 64, 3584, 128, 3328, 2816, 1792],
    #[4030, 70, 124, 74, 82, 98, 62, 449, 3905, 705, 1217, 2241],
    #[455, 3590, 3589, 3635, 3627, 3611, 7, 4024, 3960, 760, 1272, 2296],
    #[2, 4, 1, 8, 16, 32, 128, 256, 64, 512, 1024, 2048],
    #[3965, 185, 188, 181, 173, 157, 61, 3778, 3970, 3522, 3010, 1986],
    #[3835, 313, 314, 307, 299, 283, 59, 3908, 3972, 3524, 3012, 1988],
    #[2, 56, 1, 52, 44, 28, 128, 3584, 64, 3328, 2816, 1792],
    #[3965, 133, 188, 137, 145, 161, 61, 450, 3970, 706, 1218, 2242],
    #[455, 3589, 3590, 3635, 3627, 3611, 7, 3960, 4024, 760, 1272, 2296],
    #[4, 56, 1, 50, 42, 26, 256, 3584, 64, 3200, 2688, 1664],
    #[3835, 259, 314, 265, 273, 289, 59, 452, 3972, 836, 1348, 2372],
    #[455, 3587, 3590, 3637, 3629, 3613, 7, 3832, 4024, 888, 1400, 2424],
    #[64, 3970, 3972, 904, 1424, 2464, 1, 188, 314, 518, 1030, 2054],
    #[128, 3905, 3908, 840, 1360, 2400, 2, 124, 313, 517, 1029, 2053],
    #[64, 3972, 3970, 904, 1424, 2464, 1, 314, 188, 518, 1030, 2054],
    #[256, 3777, 3778, 712, 1232, 2272, 4, 122, 185, 515, 1027, 2051],
    #[64, 4024, 3970, 948, 1452, 2460, 1, 3590, 188, 3386, 2874, 1850],
    #[3584, 449, 450, 3572, 3052, 2012, 56, 70, 133, 3331, 2819, 1795],
    #[128, 3908, 3905, 840, 1360, 2400, 2, 313, 124, 517, 1029, 2053],
    #[256, 3778, 3777, 712, 1232, 2272, 4, 185, 122, 515, 1027, 2051],
    #[128, 3960, 3905, 884, 1388, 2396, 2, 3589, 124, 3385, 2873, 1849],
    #[3584, 450, 449, 3572, 3052, 2012, 56, 133, 70, 3331, 2819, 1795],
    #[256, 3832, 3777, 754, 1258, 2266, 4, 3587, 122, 3257, 2745, 1721],
    #[3584, 452, 449, 3570, 3050, 2010, 56, 259, 70, 3205, 2693, 1669]]

@[expose] def n2Gens1 : List (Array Nat) :=
  [#[62, 61, 3131, 55, 2351, 1311, 4030, 3965, 3787, 3575, 3019, 1995],
    #[49, 50, 3124, 56, 283, 299, 3136, 3200, 304, 3584, 1988, 3012],
    #[3121, 50, 3124, 3128, 850, 866, 112, 3200, 304, 560, 1997, 3021],
    #[49, 50, 52, 3128, 535, 551, 3136, 3200, 3328, 560, 1992, 3016],
    #[62, 3133, 3131, 3127, 2991, 1951, 4030, 3917, 3787, 3527, 3009, 1985],
    #[62, 61, 3131, 55, 2351, 1311, 4030, 3965, 3787, 3575, 3019, 1995],
    #[2477, 1625, 1120, 145, 2492, 1092, 742, 25, 3153, 1218, 1702, 1361],
    #[910, 3194, 3196, 70, 416, 400, 14, 753, 881, 449, 2438, 1414],
    #[1954, 2134, 2671, 3433, 2683, 1923, 3870, 3553, 425, 1845, 1193, 1886],
    #[26, 25, 3616, 2323, 2315, 1796, 1690, 1625, 2072, 1271, 751, 280],
    #[64, 128, 256, 512, 1024, 2048, 65, 130, 260, 520, 1040, 2080],
    #[3968, 125, 3191, 3195, 851, 867, 4030, 3841, 433, 689, 1933, 2957]]

@[expose] def hyp10_1 : List (Array Nat) :=
  [#[3121, 3122, 3124, 56, 488, 472, 112, 176, 304, 3584, 3015, 1991],
    #[49, 3122, 52, 56, 173, 157, 3136, 176, 3328, 3584, 3010, 1986],
    #[3073, 2, 3076, 8, 341, 357, 3184, 128, 3376, 512, 1029, 2053]]

@[expose] def resConj1 : List (Array Nat) :=
  [#[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    #[62, 61, 59, 55, 47, 31, 3968, 3904, 3776, 3520, 3008, 1984],
    #[65, 4028, 4026, 4022, 4014, 3998, 1, 190, 318, 574, 1086, 2110],
    #[3968, 125, 123, 119, 111, 95, 4030, 3841, 3713, 3457, 2945, 1921],
    #[64, 3970, 3972, 3976, 3984, 4000, 65, 3902, 3774, 3518, 3006, 1982],
    #[4030, 124, 122, 118, 110, 94, 62, 3905, 3777, 3521, 3009, 1985],
    #[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048],
    #[61, 62, 59, 55, 47, 31, 3904, 3968, 3776, 3520, 3008, 1984],
    #[3904, 190, 187, 183, 175, 159, 3965, 3842, 3650, 3394, 2882, 1858],
    #[128, 3905, 3908, 3912, 3920, 3936, 130, 3901, 3709, 3453, 2941, 1917],
    #[125, 3968, 123, 119, 111, 95, 3841, 4030, 3713, 3457, 2945, 1921],
    #[190, 3904, 187, 183, 175, 159, 3842, 3965, 3650, 3394, 2882, 1858],
    #[56, 1, 4, 50, 42, 26, 3584, 64, 256, 3200, 2688, 1664],
    #[7, 62, 59, 13, 21, 37, 448, 3968, 3776, 832, 1344, 2368],
    #[71, 3968, 123, 77, 85, 101, 385, 4030, 3713, 769, 1281, 2305],
    #[1, 2, 4, 8, 32, 16, 64, 128, 256, 512, 2048, 1024],
    #[62, 61, 59, 55, 31, 47, 3968, 3904, 3776, 3520, 1984, 3008],
    #[65, 4028, 4026, 4022, 3998, 4014, 1, 190, 318, 574, 2110, 1086],
    #[3968, 125, 123, 119, 95, 111, 4030, 3841, 3713, 3457, 1921, 2945],
    #[64, 3970, 3972, 3976, 4000, 3984, 65, 3902, 3774, 3518, 1982, 3006],
    #[4030, 124, 122, 118, 94, 110, 62, 3905, 3777, 3521, 1985, 3009],
    #[2, 1, 4, 8, 32, 16, 128, 64, 256, 512, 2048, 1024],
    #[61, 62, 59, 55, 31, 47, 3904, 3968, 3776, 3520, 1984, 3008],
    #[3904, 190, 187, 183, 159, 175, 3965, 3842, 3650, 3394, 1858, 2882],
    #[128, 3905, 3908, 3912, 3936, 3920, 130, 3901, 3709, 3453, 1917, 2941],
    #[125, 3968, 123, 119, 95, 111, 3841, 4030, 3713, 3457, 1921, 2945],
    #[190, 3904, 187, 183, 159, 175, 3842, 3965, 3650, 3394, 1858, 2882],
    #[56, 1, 4, 50, 26, 42, 3584, 64, 256, 3200, 1664, 2688],
    #[7, 62, 59, 13, 37, 21, 448, 3968, 3776, 832, 2368, 1344],
    #[71, 3968, 123, 77, 101, 85, 385, 4030, 3713, 769, 2305, 1281]]

@[expose] def n2Gens (i : Nat) : List (Array Nat) := if i = 0 then n2Gens0 else n2Gens1

@[expose] def hyp10 (i : Nat) : List (Array Nat) := if i = 0 then hyp10_0 else hyp10_1

@[expose] def resConj (i : Nat) : List (Array Nat) := if i = 0 then resConj0 else resConj1

@[expose] def conjRows (c : Array Nat) (gs : List (Array Nat)) : List (Array Nat) :=
  gs.map fun g => mulR (mulR c g) (invR c)

@[expose] def nlGens0 : List (Array Nat) :=
  [#[817, 3902, 3317, 3321, 2927, 1887, 3197, 3970, 3398, 3658, 3010, 1986],
    #[3275, 196, 3846, 821, 2518, 1510, 760, 263, 442, 3449, 1457, 2481],
    #[3787, 3338, 265, 259, 2991, 1951, 752, 702, 589, 199, 3009, 1985]]

@[expose] def nlInv0 : List (Array Nat) :=
  [#[3901, 818, 3318, 3322, 2991, 1951, 3905, 3262, 3461, 3721, 3009, 1985],
    #[3273, 3317, 3902, 769, 2392, 1384, 634, 3398, 3970, 77, 1597, 2621],
    #[125, 3195, 4016, 3191, 2272, 1232, 3964, 3786, 3086, 3526, 2051, 1027]]

@[expose] def nlGens1 : List (Array Nat) :=
  [#[444, 3461, 3700, 587, 2456, 1448, 3898, 371, 3341, 706, 1598, 2622],
    #[637, 3459, 3466, 3698, 2918, 1878, 3956, 245, 700, 3211, 2443, 1419],
    #[65, 956, 4026, 4022, 2846, 1838, 64, 3890, 3716, 3464, 1970, 2994]]

@[expose] def nlInv1 : List (Array Nat) :=
  [#[778, 3272, 3271, 825, 2453, 1445, 646, 571, 500, 3701, 1395, 2419],
    #[3651, 446, 3505, 3653, 2985, 1945, 250, 4024, 3143, 380, 2631, 1607],
    #[65, 956, 4026, 4022, 2846, 1838, 64, 3890, 3716, 3464, 1970, 2994]]

@[expose] def nlGens (i : Nat) : List (Array Nat) := if i = 0 then nlGens0 else nlGens1

@[expose] def nlInv (i : Nat) : List (Array Nat) := if i = 0 then nlInv0 else nlInv1

@[expose] def repPair (i k : Nat) : Array Nat × Array Nat :=
  if i = 0 then
    if k = 0 then
      (#[3073, 3074, 4, 8, 227, 211, 3184, 3248, 256, 512, 2051, 1027],
        #[1, 3074, 4, 3080, 666, 682, 64, 3248, 256, 3632, 1034, 2058])
    else
      (#[3073, 3074, 4, 8, 227, 211, 3184, 3248, 256, 512, 2051, 1027],
        #[3073, 3074, 3076, 3080, 1007, 991, 3184, 3248, 3376, 3632, 2063, 1039])
  else
    if k = 0 then
      (#[3121, 3122, 3124, 56, 488, 472, 112, 176, 304, 3584, 3015, 1991],
        #[1, 2, 3076, 3080, 812, 796, 64, 128, 3376, 3632, 2060, 1036])
    else
      (#[3121, 3122, 3124, 56, 488, 472, 112, 176, 304, 3584, 3015, 1991],
        #[49, 3122, 52, 56, 173, 157, 3136, 176, 3328, 3584, 3010, 1986])

@[expose, noinline] def nlOKAt (S : List Nat) (C : List (Array Nat))
    (W : List (Array Nat × Array Nat)) : Bool :=
  W.all fun (g, gi) =>
    gammaUN g && gammaUN gi && mulR g gi == idR && mulR gi g == idR && appN g a0 == a0 &&
      d0.all (fun d => S.contains (appN g d)) && d0.all (fun d => S.contains (appN gi d)) &&
      C.all (fun x => C.contains (mulR (mulR g x) gi)) &&
      C.all (fun x => C.contains (mulR (mulR gi x) g))

@[expose] def nlOK (i : Nat) : Bool := nlOKAt (spanList d0) (compOf i) ((nlGens i).zip (nlInv i))

@[expose] def conjTr (gens : List (Array Nat × Array Nat)) (fuel : Nat)
    (start : Array Nat × Array Nat) :
    List ((Array Nat × Array Nat) × Array Nat × Array Nat) :=
  bfsClosure (fun p => p.1)
    (gens.map fun gg p => ((mulR (mulR gg.1 p.1.1) gg.2, mulR (mulR gg.1 p.1.2) gg.2),
      mulR gg.1 p.2.1, mulR p.2.2 gg.2)) fuel
    [(start, idR, idR)] ((∅ : Std.HashSet (Array Nat × Array Nat)).insert start) []

@[expose] def pairT (i k : Nat) : List ((Array Nat × Array Nat) × Array Nat × Array Nat) :=
  conjTr ((nlGens i).zip (nlInv i)) 300 (repPair i k)

@[expose, noinline] def pairCoverAt (U : List (Array Nat))
    (K : Std.HashSet (Array Nat × Array Nat)) : Bool :=
  U.all fun x => U.all fun y => x == y || K.contains (x, y)

@[expose] def pairCover (i : Nat) : Bool :=
  pairCoverAt (unitaryElts i) (Std.HashSet.ofList ((pairT i 0 ++ pairT i 1).map (·.1)))

@[expose] def normsAt (HS : Std.HashSet (Array Nat)) (gens : List (Array Nat))
    (u ui : Array Nat) : Bool :=
  gens.all fun n => HS.contains (mulR (mulR u n) ui)

@[expose, noinline] def resPermAt (HS : Std.HashSet (Array Nat)) (gens : List (Array Nat))
    (W CI : List (Array Nat × Array Nat)) : Bool :=
  W.all fun (g, gi) => CI.all fun (c, ci) => CI.any fun (c', ci') =>
    normsAt HS gens (mulR ci' (mulR g c)) (mulR ci (mulR gi c'))

@[expose] def invGuess (g : Array Nat) : Array Nat := if mulR g g == idR then g else mulR g g

@[expose] def withInvGuess (gs : List (Array Nat)) : List (Array Nat × Array Nat) :=
  gs.map fun g => (g, invGuess g)

@[expose] def residualIn (HS : Std.HashSet (Array Nat)) (n2 gs : List (Array Nat))
    (CI : List (Array Nat × Array Nat)) : Bool :=
  let Y := enumGrp gs
  (withInv gs).all pairOK && closedCheck gs Y &&
    (let HY := Std.HashSet.ofList Y
     CI.any fun (c, ci) =>
       n2.all (fun n => HY.contains (mulR (mulR c n) ci)) &&
         gs.all fun g => HS.contains (mulR (mulR ci g) c))

@[expose, noinline] def pairRepAt (i : Nat) (HS : Std.HashSet (Array Nat))
    (CI : List (Array Nat × Array Nat))
    (R1 R2 : List (List (Array Nat) × List (Array Nat) × Std.HashSet (Array Nat))) : Bool :=
  R1.all fun p₁ => R2.all fun p₂ =>
    violCheckW (withInvGuess (p₁.1 ++ p₂.1)) (compOf i) (compGens i) (compOf i) false ||
      residualIn HS (n2Gens i) (p₁.1 ++ p₂.1) CI

@[expose, noinline] def pCheckClass (i : Nat) (ST : List (Nat × Array Nat × Array Nat))
    (DT : List (List Nat × Array Nat × Array Nat)) (CA : List (List (Array Nat))) : Bool :=
  let X := enumGrp (n2Gens i)
  let CI := (resConj i).map fun c => (c, invR c)
  nlOK i && pairCover i &&
    ([0, 1].all fun k =>
      (unitaryElts i).contains (repPair i k).1 && (unitaryElts i).contains (repPair i k).2) &&
    (withInv (n2Gens i)).all pairOK && closedCheck (n2Gens i) X && CI.all pairOK &&
    (let HS := Std.HashSet.ofList X
     resPermAt HS (n2Gens i) ((nlGens i).zip (nlInv i)) CI &&
       [0, 1].all fun k =>
         pairRepAt i HS CI (censusOf (probe i) (candsOf ST DT CA i (repPair i k).1)).1
           (censusOf (probe i) (candsOf ST DT CA i (repPair i k).2)).1)

@[expose] def pCheck (_ : Unit := ()) : Bool :=
  let ST := singT ()
  let DT := dT ()
  let CA := compAll ()
  pCheckClass 0 ST DT CA && pCheckClass 1 ST DT CA

@[expose, noinline] def tCheckClass (i : Nat) (ST : List (Nat × Array Nat × Array Nat))
    (DT : List (List Nat × Array Nat × Array Nat)) (CA : List (List (Array Nat))) : Bool :=
  let W2 := withInv (n2Gens i)
  W2.all pairOK &&
    (unitaryElts i).all fun r => (hyp10 i).contains r ||
      (censusOf (probe i) (candsOf ST DT CA i r)).1.all fun p =>
        violCheckW (W2 ++ withInvGuess p.1) (compOf i) (compGens i) (compOf i) false

@[expose] def tCheck (_ : Unit := ()) : Bool :=
  let ST := singT ()
  let DT := dT ()
  let CA := compAll ()
  tCheckClass 0 ST DT CA && tCheckClass 1 ST DT CA

end CFSG.GammaU.Native
