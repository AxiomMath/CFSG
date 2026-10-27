module

public import CFSG.Certificates.IndexOrbit
public import CFSG.Certificates.SetOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Inputs
public import CFSG.Monster.B.Fischer.PinnedChainData
public import CFSG.RankThree.Native.Fi22FiveArrays
public meta import CFSG.Certificates.IndexOrbit
public meta import CFSG.Certificates.SetOrbit
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Inputs
public meta import CFSG.Monster.B.Fischer.PinnedChainData
public meta import CFSG.RankThree.Native.Fi22FiveArrays

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates.SetOrbit CFSG.Certificates.IndexOrbit
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

@[expose] def fi22OmegaU0 : Array ℕ := #[0,1,2,19,30,50,52,75,78,79,99,120,134,135,150,153,163,173,204,206,211,215,234,241,257,265,269,314,329,350,356,361,362,380,382,386,387,388,391,393,405,408,422,428,437,444,451,460,461,519,523,535,539,561,566,576,578,579,584,595,596,601,606,607,612,615,626,627,635,646,656,667,683,695,716,726,747,753,761,766,797,804,806,809,813,848,850,859,866,888,894,899,922,927,944,956,960,969,977,982,983,985,986,994,1011,1034,1048,1053,1067,1073,1078,1086,1097,1105,1112,1113,1136,1149,1152,1158,1161,1165,1172,1180,1198,1214,1221,1230,1235,1238,1282,1289,1312,1316,1318,1323,1330,1336,1349,1356,1362,1371,1374,1383,1386,1391,1394,1434,1446,1447,1460,1478,1485,1494,1501,1539,1554,1555,1561,1565,1566,1568,1574,1578,1585,1600,1609,1613,1614,1630,1659,1697,1703,1708,1717,1733,1756,1761,1796,1797,1806,1814,1820,1825,1847,1860,1865,1875,1888,1905,1921,1931,1932,1945,1982,2003,2018,2024,2026,2029,2034,2058,2065,2067,2075,2081,2084,2086,2112,2118,2119,2120,2136,2150,2168,2201,2205,2217,2226,2227,2231,2233,2243,2245,2260,2269,2304,2340,2344,2351,2365,2382,2397,2399,2400,2413,2420,2428,2431,2459,2471,2478,2486,2488,2493,2494,2498,2517,2520,2523,2528,2542,2562,2575,2578,2579,2580,2581,2587,2614,2620,2636,2645,2684,2694,2717,2719,2722,2730,2731,2744,2746,2748,2761,2767,2770,2816,2820,2822,2834,2854,2857,2858,2862,2864,2869,2871,2882,2890,2903,2923,2927,2936,2940,2947,2950,2951,2956,2962,2964,3026,3027,3029,3040,3045,3052,3095,3096,3106,3113,3117,3126,3143,3148,3168,3171,3176,3181,3182,3186,3189,3196,3212,3218,3238,3242,3249,3255,3262,3277,3324,3328,3331,3341,3351,3353,3356,3367,3376,3377,3381,3385,3390,3400,3408,3411,3412,3428,3432,3433,3448,3456,3460,3461,3463,3470,3483,3484,3485,3494]

@[expose] def fi22OmegaGens (_ : Unit := ()) : Array (Array ℕ) :=
  #[fi22ChainGen 0, fi22ChainGen 1]

@[expose] def fi22OmegaYs (_ : Unit := ()) : Array (Array ℕ) :=
  (List.range 8).toArray.map i242YArr

@[expose] def fi22OmegaHWord : ℕ → List ℕ
  | 0 => [6, 5, 4, 5, 7, 3]
  | _ => [2, 0, 5, 1, 2, 7]

@[expose] def fi22OmegaWordArr (ys : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldl (fun acc r => compA 3510 ys[r]! acc) (idA 3510)

@[expose] def fi22OmegaHs (_ : Unit := ()) : Array (Array ℕ) :=
  let ys := fi22OmegaYs ()
  #[fi22OmegaWordArr ys (fi22OmegaHWord 0), fi22OmegaWordArr ys (fi22OmegaHWord 1)]

@[expose] def fi22OmegaTab (_ : Unit := ()) : Array (Array ℕ) :=
  bfsL (fi22OmegaGens ()) fi22OmegaU0 70000

@[expose] def fi22OmegaIndsOf (tab : Array (Array ℕ)) (perms : Array (Array ℕ)) :
    Array (Array ℕ) :=
  let m := keyMap tab
  perms.map (induceL tab m)

@[expose] def fi22OmegaCheckWith (tab ys : Array (Array ℕ)) (gi hi : Array (Array ℕ))
    (po ho : Array IdxOrbit × Array ℕ × Array ℕ) : Bool :=
  tab.size == 61776 &&
  (tab[0]! == fi22OmegaU0 &&
  ((List.range tab.size).all (fun i => entryOK 3510 360 tab[i]!) &&
  (distinctOK tab &&
  (gi.size == 2 &&
  ((List.range 2).all (fun k => boundOK tab.size gi[k]!) &&
  (hi.size == 2 &&
  ((List.range 2).all (fun k => boundOK tab.size hi[k]!) &&
  (po.1.size == 1 &&
  ((po.1[0]!).pts[0]! == 0 &&
  (idxTreeOK gi po.1[0]! &&
  (idxClosedOK gi po.1[0]! po.2.2 &&
  (idxPartitionOK tab.size po.1 po.2.1 po.2.2 &&
  ((ho.1.map fun o => o.pts.size) == #[1, 37800, 22400, 1575] &&
  ((ho.1[0]!).pts[0]! == 0 &&
  ((List.range 4).all (fun c => idxTreeOK hi ho.1[c]! && idxClosedOK hi ho.1[c]! ho.2.2) &&
  (idxPartitionOK tab.size ho.1 ho.2.1 ho.2.2 &&
  ((List.range 8).all (fun r =>
    decide (imgList ys[r]! fi22OmegaU0 = fi22OmegaU0.toList)) &&
  ((List.range 2).all (fun k =>
    decide (imgList fi22FiveQGenArrs[k]! fi22OmegaU0 = fi22OmegaU0.toList))))))))))))))))))))

@[expose] def fi22OmegaCheck (tab : Array (Array ℕ)) : Bool :=
  let gi := fi22OmegaIndsOf tab (fi22OmegaGens ())
  let hi := fi22OmegaIndsOf tab (fi22OmegaHs ())
  fi22OmegaCheckWith tab (fi22OmegaYs ()) gi hi (idxOrbits gi tab.size) (idxOrbits hi tab.size)

end CFSG.Monster.B.Fischer
