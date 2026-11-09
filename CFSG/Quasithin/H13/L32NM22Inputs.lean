module

public import CFSG.Quasithin.H13.L32NMatNInputs
public import CFSG.Quasithin.H13.L32NS7Inputs

public section

namespace CFSG.Quasithin.H13.M22Cert

open MatNCert

abbrev one12 : List ℕ := oneN 12

@[expose] def gG : List (List ℕ) :=
  [[2054, 5, 2052, 2080, 2112, 2056, 2064, 512, 3072, 128, 2304, 2048],
    [1040, 3224, 1041, 2194, 20, 3584, 3072, 544, 704, 3712, 1024, 2816]]

@[expose] def gInv : List (List ℕ) := [gG.getD 0 [], powN 12 (gG.getD 1 []) 3]

abbrev tW (w : List ℕ) : List ℕ := evalW 12 gG w

@[expose] def v0 : ℕ := 4

@[expose] def orbBfs (gs : List (List ℕ)) :
    ℕ → Std.HashSet ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ) → List (ℕ × List ℕ)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      let st := fr.foldl
        (fun (st : Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) uw =>
          (List.range gs.length).foldl
            (fun (st : Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) i =>
              let y := mvN (gs.getD i []) uw.1
              if st.1.contains y then st
              else (st.1.insert y, (y, i :: uw.2) :: st.2.1, (y, i :: uw.2) :: st.2.2)) st)
        (seen, acc, [])
      orbBfs gs fuel st.1 st.2.1 st.2.2

@[expose] def orbL : List (ℕ × List ℕ) :=
  (orbBfs gG 100 ((∅ : Std.HashSet ℕ).insert v0) [(v0, [])] [(v0, [])]).reverse

@[expose] def orbB : Bool :=
  orbL.head? == some (v0, []) && orbL.length == 693 &&
    decide (((orbL.map Prod.fst).mergeSort).IsChain (· < ·)) &&
    orbL.all fun uw => mvN (tW uw.2) v0 == uw.1

@[expose] def s0W : List (List ℕ) :=
  [[1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0]]

@[expose] def s0G : List (List ℕ) := s0W.map tW

@[expose] def pG : List (List ℕ) :=
  [[1, 276, 4, 267, 16, 2418, 3073, 2261, 22, 1795, 1024, 1089],
    [1, 2654, 4, 2625, 16, 2409, 837, 1924, 3932, 3164, 1024, 3856],
    [16, 176, 4, 175, 1, 3288, 2475, 3291, 434, 1714, 1024, 510],
    [147, 1446, 4, 3831, 313, 2532, 2307, 3932, 3576, 1692, 1024, 967],
    [163, 115, 4, 125, 178, 4040, 1350, 2828, 1380, 1747, 1028, 2058]]

@[expose] def pE : List (List ℕ) := elemsOf 12 pG

@[expose] def pB : Bool :=
  subB 12 pG pE && pE.length == 256 &&
    (List.range 4096).all fun v => !(pG.all fun g => mvN g v == v) || v == 0 || v == v0

@[expose] def e0G : List (List ℕ) :=
  [[1, 2654, 4, 2625, 16, 2409, 837, 1924, 3932, 3164, 1024, 3856],
    [16, 439, 4, 445, 1, 1422, 1518, 1179, 181, 928, 1024, 3515],
    [772, 1788, 4, 860, 785, 2664, 68, 2087, 1601, 1604, 1028, 3860],
    [1029, 1285, 4, 1306, 1044, 3433, 766, 3291, 3, 1795, 1024, 2731],
    [2380, 3450, 4, 2270, 2393, 36, 2572, 3158, 2172, 561, 1024, 2731]]

@[expose] def e0E : List (List ℕ) := elemsOf 12 e0G

@[expose] def cjL : List (List ℕ × List ℕ) :=
  s0W.map (fun w => (tW w, evalW 12 gInv w.reverse)) ++
    s0W.map (fun w => (evalW 12 gInv w.reverse, tW w))

@[expose] def e0B : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  let hE : Std.HashSet (List ℕ) := Std.HashSet.ofList e0E
  subB 12 e0G e0E && e0E.length == 32 && e0G.all hP.contains &&
    (cjL.all fun c => mulN c.1 c.2 == one12) &&
    pE.all fun x => hE.contains x || cjL.any fun c => !(hP.contains (mulN (mulN c.1 x) c.2))

@[expose] def q12c : List ℕ := [1, 3, 2, 7, 16, 58, 99, 172, 487, 815, 970, 1323]

@[expose] def wits : List (ℕ × List ℕ × ℕ) :=
  [(443, [772, 1788, 4, 860, 785, 2664, 68, 2087, 1601, 1604, 1028, 3860], 168),
    (447, [772, 1788, 4, 860, 785, 2664, 68, 2087, 1601, 1604, 1028, 3860], 185),
    (1467, [16, 439, 4, 445, 1, 1422, 1518, 1179, 181, 928, 1024, 3515], 546),
    (1471, [16, 439, 4, 445, 1, 1422, 1518, 1179, 181, 928, 1024, 3515], 33)]

@[expose] def witB : Bool :=
  let hE : Std.HashSet (List ℕ) := Std.HashSet.ofList e0E
  wits.all fun p => hE.contains p.2.1 && !(polN 12 q12c p.2.2 v0) &&
    mvN p.2.1 p.2.2 ^^^ p.2.2 == p.1

@[expose] def U4 : List ℕ := [1467, 1471, 443, 447]

@[expose] def rP : List (List ℕ × List ℕ) :=
  [([1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
      [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]),
    ([1, 2, 4, 3507, 1796, 3915, 1412, 3387, 1078, 3435, 2377, 2048],
      [1, 2, 4, 3507, 1796, 3915, 1412, 3387, 1078, 3435, 2377, 2048]),
    ([1, 35, 4, 3517, 3672, 32, 3573, 2505, 3220, 2197, 769, 1428],
      [1, 35, 4, 3517, 3672, 32, 3573, 2505, 3220, 2197, 769, 1428]),
    ([1, 276, 4, 245, 785, 2891, 3271, 2347, 3186, 1338, 2396, 1089],
      [1, 822, 4, 2438, 1796, 511, 328, 1982, 1794, 23, 2377, 3276]),
    ([1, 712, 4, 2625, 2648, 511, 655, 1215, 1339, 3187, 1812, 3829],
      [1, 712, 4, 2625, 2648, 511, 655, 1215, 1339, 3187, 1812, 3829]),
    ([5, 1431, 4, 1458, 2376, 725, 676, 3176, 1387, 1403, 1793, 2085],
      [5, 1865, 4, 1458, 768, 11, 878, 1233, 3782, 1182, 3677, 2058]),
    ([5, 1431, 4, 2088, 1813, 3504, 3590, 498, 2319, 2590, 2653, 2085],
      [5, 2082, 4, 2057, 2397, 3504, 3623, 1779, 1179, 3779, 788, 1457]),
    ([5, 1863, 4, 2057, 1025, 725, 3871, 1589, 2560, 3332, 21, 1870],
      [5, 1865, 4, 2055, 1025, 3487, 1102, 2404, 2587, 2314, 21, 2058]),
    ([5, 1865, 4, 1458, 768, 11, 878, 1233, 3782, 1182, 3677, 2058],
      [5, 1431, 4, 1458, 2376, 725, 676, 3176, 1387, 1403, 1793, 2085]),
    ([5, 2082, 4, 2057, 2397, 3504, 3623, 1779, 1179, 3779, 788, 1457],
      [5, 1431, 4, 2088, 1813, 3504, 3590, 498, 2319, 2590, 2653, 2085]),
    ([97, 271, 4, 1214, 112, 1825, 3352, 829, 1453, 3201, 430, 3947],
      [2620, 3734, 4, 2851, 2605, 2243, 766, 1789, 3983, 3322, 426, 3947]),
    ([97, 1080, 4, 3249, 2620, 384, 616, 591, 3158, 3481, 2294, 506],
      [3118, 2487, 4, 4047, 631, 1373, 2418, 2234, 2202, 928, 2279, 2897]),
    ([101, 325, 4, 352, 2348, 1488, 1696, 3994, 3434, 1878, 3063, 2778],
      [885, 2796, 4, 3954, 2616, 891, 11, 664, 888, 2640, 3059, 3941]),
    ([101, 1572, 4, 352, 864, 689, 2201, 66, 3050, 2970, 2275, 2095],
      [2601, 597, 4, 1301, 2348, 2297, 725, 3012, 2596, 24, 2279, 3476]),
    ([151, 684, 4, 3039, 2507, 365, 32, 2519, 733, 996, 4087, 2740],
      [614, 2092, 4, 2581, 2689, 64, 2469, 206, 434, 2717, 3677, 2198])]

@[expose] def rPS0W : List (List ℕ) :=
  [[], [0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    [1, 0, 0, 1, 0, 1, 0], [1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    [1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 1, 1, 1], [1, 1, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0], [0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    [1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1],
    [1, 0, 1, 0, 0, 1, 0]]

@[expose] def pS0W : List (List ℕ) :=
  [[0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0], [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    [1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]]

@[expose] def s0B : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  pG.length == 5 && (List.range 5).all (fun k => pG.getD k [] == evalW 12 s0G (pS0W.getD k [])) &&
    (rP.any fun r => hP.contains (mulN r.2 one12)) &&
    (s0G.all fun g => rP.all fun r => rP.any fun r' => hP.contains (mulN r'.2 (mulN g r.1))) &&
    (rP.all fun r => mvN r.1 v0 == v0) && pE.all fun p => mvN p v0 == v0

@[expose] def schB : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  let K := (List.range 64).map fun b => orbL.filter fun p => p.1 % 64 == b
  orbL.all fun uw => gG.all fun g =>
    match (K.getD (mvN g uw.1 % 64) []).find? (fun p => p.1 == mvN g uw.1) with
    | some uw' =>
      let s := mulN (evalW 12 gInv uw'.2.reverse) (mulN g (tW uw.2))
      (rP.any fun r => hP.contains (mulN r.2 s)) && mulN (tW uw'.2) s == mulN g (tW uw.2)
    | none => false

@[expose] def mW : List (List ℕ) :=
  [[0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0], [1, 0, 1, 1, 1, 0, 1, 0, 1]]

@[expose] def mRep : List (List ℕ) :=
  [mulN (tW (mW.getD 0 [])) (rP.getD 4 ([], [])).1,
    mulN (tW (mW.getD 1 [])) (rP.getD 11 ([], [])).1]

@[expose] def mE (i : ℕ) : List (List ℕ) := elemsOf 12 (pG ++ [mRep.getD i one12])

@[expose] def ovZW : List (List ℕ) := [[5, 5, 3, 5], [5, 4, 5], [5, 0, 5], [5, 3, 5]]

@[expose] def ovFourB (hP : Std.HashSet (List ℕ)) (y : List ℕ) : Bool :=
  let a := evalW 12 (pG ++ [y]) [0, 5]
  mvN y v0 != v0 && mvN a v0 != v0 && mvN a v0 != mvN y v0 &&
    ovZW.any fun w =>
      let z := evalW 12 (pG ++ [y]) w
      (mvN z v0 != v0 && mvN z v0 != mvN y v0 && mvN z v0 != mvN a v0) ||
        (mvN z v0 == v0 && !hP.contains z)

@[expose] def mInv : List (List (List ℕ)) :=
  [[one12, [2098, 632, 447, 2198, 2456, 1848, 2988, 3960, 768, 3164, 3935, 2571],
      [2098, 2855, 447, 476, 2456, 3711, 3430, 3786, 2655, 2633, 3935, 3265]],
    [one12, [883, 1274, 1467, 2576, 723, 3192, 841, 3157, 60, 2646, 3935, 2189],
      [883, 1876, 1467, 3493, 723, 425, 1185, 906, 914, 700, 3935, 3941]]]

@[expose] def mCosP (i : ℕ) : List (List ℕ × List ℕ) :=
  ([[], [5], [0, 5]].map (evalW 12 (pG ++ [mRep.getD i one12]))).zip (mInv.getD i [])

@[expose] def ovB : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  let h0 : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE 0)
  let h1 : Std.HashSet (List ℕ) := Std.HashSet.ofList (mE 1)
  (orbL.all fun uw => uw.1 == v0 || U4.contains uw.1 ||
    pE.any fun p₁ => mvN p₁ uw.1 != uw.1 &&
      pE.any fun p₂ => mvN p₂ uw.1 != uw.1 && mvN p₂ uw.1 != mvN p₁ uw.1) &&
  ((List.range 15).all (fun k => (rP.getD k ([], [])).1 == evalW 12 s0G (rPS0W.getD k [])) &&
    rP.all fun r => mulN r.1 r.2 == one12) &&
  (rP.length == 15 && (List.range 15).all fun i => (List.range i).all fun j =>
    !(hP.contains (mulN (rP.getD j ([], [])).2 (rP.getD i ([], [])).1))) &&
  (orbL.all fun uw => !(U4.contains uw.1) || rP.all fun r =>
    let y := mulN (tW uw.2) r.1
    h0.contains y || h1.contains y || ovFourB hP y) &&
  [0, 1].all fun i => nodupB 12 (mE i) && (mE i).length == 768 && (mCosP i).length == 3 &&
    (mCosP i).all (fun c => validB 12 c.2 && mulN c.1 c.2 == one12) &&
    (mCosP i).any (fun c => hP.contains (mulN c.2 one12)) &&
    (pG ++ [mRep.getD i one12]).all fun g => (mCosP i).all fun c => (mCosP i).any fun c' =>
      hP.contains (mulN c'.2 (mulN g c.1))

@[expose] def oddOf (M : List (List ℕ)) : List (List ℕ) :=
  M.filter fun x => powN 12 x 3 == one12

@[expose] def twoOf (O : List (List ℕ)) : List (List ℕ) := O.filter fun x => sqN x 2 == one12

@[expose] def oW : List (List (List ℕ)) := [[[5, 3], [3, 5], [5, 5]], [[5, 2, 1, 0]]]

@[expose] def oG (i : ℕ) : List (List ℕ) :=
  (oW.getD i []).map (evalW 12 (pG ++ [mRep.getD i one12]))

@[expose] def oE (i : ℕ) : List (List ℕ) := elemsOf 12 (oG i)

@[expose] def oWs : List (ℕ × ℕ) := [(443, 447), (1467, 1471)]

@[expose] def oB : Bool :=
  [0, 1].all fun i =>
    let w := oWs.getD i (0, 0)
    let O := oE i
    let R := twoOf O
    let hR : Std.HashSet (List ℕ) := Std.HashSet.ofList R
    let hO : Std.HashSet (List ℕ) := Std.HashSet.ofList O
    subB 12 (oG i) O && ((oG i).all fun g => powN 12 g 3 == one12) &&
      (oddOf (mE i)).all hO.contains && nodupB 12 R && O.length == 3 * R.length &&
      (R.all fun a => R.all fun b => hR.contains (mulN a b)) &&
      (O.all fun o => !(sqN o 8 == one12) || sqN o 2 == one12) &&
      (O.all fun y => [0, w.1, w.2, w.1 ^^^ w.2].contains (mvN y v0 ^^^ v0)) &&
      (O.any fun y => mvN y v0 ^^^ v0 == w.1) && (O.any fun y => mvN y v0 ^^^ v0 == w.2) &&
      O.any fun y => polN 12 q12c (mvN y 1 ^^^ 1) w.1

@[expose] def m12G : List (List ℕ) := pG ++ mRep

@[expose] def m12CosW : List (List ℕ) :=
  [[], [5], [6], [0, 5], [6, 5], [0, 6], [5, 6], [0, 6, 5], [0, 5, 6]]

@[expose] def m12Inv : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    [2098, 632, 447, 2198, 2456, 1848, 2988, 3960, 768, 3164, 3935, 2571],
    [883, 1274, 1467, 2576, 723, 3192, 841, 3157, 60, 2646, 3935, 2189],
    [2098, 2855, 447, 476, 2456, 3711, 3430, 3786, 2655, 2633, 3935, 3265],
    [26, 4037, 3931, 4047, 2906, 2254, 1108, 3821, 1929, 1956, 2911, 1128],
    [883, 1876, 1467, 3493, 723, 425, 1185, 906, 914, 700, 3935, 3941],
    [732, 3492, 2784, 1866, 3111, 398, 3425, 2634, 2666, 2531, 1024, 3906],
    [26, 904, 3931, 1945, 2906, 3044, 3885, 2762, 3012, 1197, 2911, 3857],
    [732, 3245, 2784, 600, 3111, 2116, 2462, 3186, 2915, 2289, 1024, 3005]]

@[expose] def m12Cos : List (List ℕ × List ℕ) := (m12CosW.map (evalW 12 m12G)).zip m12Inv

@[expose] def m12SurW : List (List ℕ × List ℕ × List ℕ) :=
  [([0, 1, 2], [0, 1, 2], []), ([0, 1, 2], [0, 2, 1], [4, 0]), ([0, 1, 2], [1, 0, 2], [6, 4]),
    ([0, 1, 2], [1, 2, 0], [6, 0]), ([0, 1, 2], [2, 0, 1], [0, 6]),
    ([0, 1, 2], [2, 1, 0], [0, 6, 4, 0]), ([0, 2, 1], [0, 1, 2], [4]), ([0, 2, 1], [0, 2, 1], [0]),
    ([0, 2, 1], [1, 0, 2], [6]), ([0, 2, 1], [1, 2, 0], [6, 4, 0]),
    ([0, 2, 1], [2, 0, 1], [0, 6, 4]), ([0, 2, 1], [2, 1, 0], [0, 6, 0]),
    ([1, 0, 2], [0, 1, 2], [5, 4]), ([1, 0, 2], [0, 2, 1], [5, 0]), ([1, 0, 2], [1, 0, 2], [5, 6]),
    ([1, 0, 2], [1, 2, 0], [5, 6, 4, 0]), ([1, 0, 2], [2, 0, 1], [0, 6, 5, 4]),
    ([1, 0, 2], [2, 1, 0], [0, 6, 5, 0]), ([1, 2, 0], [0, 1, 2], [5]),
    ([1, 2, 0], [0, 2, 1], [5, 4, 0]), ([1, 2, 0], [1, 0, 2], [5, 6, 4]),
    ([1, 2, 0], [1, 2, 0], [5, 6, 0]), ([1, 2, 0], [2, 0, 1], [0, 6, 5]),
    ([1, 2, 0], [2, 1, 0], [0, 6, 5, 4, 0]), ([2, 0, 1], [0, 1, 2], [5, 5]),
    ([2, 0, 1], [0, 2, 1], [4, 5, 0]), ([2, 0, 1], [1, 0, 2], [6, 5, 4]),
    ([2, 0, 1], [1, 2, 0], [6, 5, 0]), ([2, 0, 1], [2, 0, 1], [0, 5, 6]),
    ([2, 0, 1], [2, 1, 0], [0, 5, 6, 4, 0]), ([2, 1, 0], [0, 1, 2], [4, 5]),
    ([2, 1, 0], [0, 2, 1], [0, 5]), ([2, 1, 0], [1, 0, 2], [6, 5]),
    ([2, 1, 0], [1, 2, 0], [6, 5, 4, 0]), ([2, 1, 0], [2, 0, 1], [0, 5, 6, 4]),
    ([2, 1, 0], [2, 1, 0], [0, 5, 6, 0])]

@[expose] def blkA : List (List ℕ) := [[4, 1467, 1471], [443, 2784, 2907], [447, 3812, 3931]]

@[expose] def blkB : List (List ℕ) := [[4, 443, 447], [1467, 2784, 3931], [1471, 2907, 3812]]

@[expose] def m12B : Bool :=
  let hP : Std.HashSet (List ℕ) := Std.HashSet.ofList pE
  (m12Cos.all fun c => validB 12 c.2 && mulN c.1 c.2 == one12) &&
    (m12Cos.any fun c => hP.contains (mulN c.2 one12)) &&
    (m12G.all fun g => m12Cos.all fun c => m12Cos.any fun c' =>
      hP.contains (mulN c'.2 (mulN g c.1))) &&
    (m12Cos.all fun c => blkInvB blkA c.1 && blkInvB blkB c.1 &&
      S7Cert.perm3L.contains (blkPerm blkA c.1) && S7Cert.perm3L.contains (blkPerm blkB c.1)) &&
    (pE.all fun x => blkInvB blkA x && blkInvB blkB x &&
      S7Cert.perm3L.contains (blkPerm blkA x) && S7Cert.perm3L.contains (blkPerm blkB x)) &&
    (S7Cert.perm3L.all fun l => S7Cert.perm3L.all fun l' =>
      m12SurW.any fun t => t.1 == l && t.2.1 == l') &&
    (m12SurW.all fun t => blkPerm blkA (evalW 12 m12G t.2.2) == t.1 &&
      blkPerm blkB (evalW 12 m12G t.2.2) == t.2.1) &&
    m12Cos.all fun c => pE.all fun p =>
      !(S7Cert.compL (blkPerm blkA c.1) (blkPerm blkA p) == [0, 1, 2] &&
        S7Cert.compL (blkPerm blkB c.1) (blkPerm blkB p) == [0, 1, 2]) ||
      sqN (mulN c.1 p) 2 == one12

@[expose] def m22Check : Bool :=
  gG.all (validB 12) && orbB && s0B && schB && pB && e0B && witB && ovB && oB && m12B

end CFSG.Quasithin.H13.M22Cert
