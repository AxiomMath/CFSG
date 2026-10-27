module

public import CFSG.Quasithin.H13.L32NM22Inputs

public section

namespace CFSG.Quasithin.H.Mathieu.H12Cert

open CFSG.Quasithin.H13.MatNCert

abbrev one12 : List ℕ := oneN 12

@[expose] def gG : List (List ℕ) :=
  [[4, 8, 1, 2, 256, 512, 890, 415, 16, 32, 1845, 2330],
    [16, 32, 64, 128, 337, 674, 1024, 2048, 1025, 2050, 1092, 2184]]

@[expose] def gInv : List (List ℕ) := [gG.getD 0 [], powN 12 (gG.getD 1 []) 3]

abbrev tW (w : List ℕ) : List ℕ := evalW 12 gG w

@[expose] def z12 : List ℕ := [2, 3, 8, 12, 32, 48, 128, 192, 512, 768, 2048, 3072]

@[expose] def zW : List ℕ := (List.replicate 11 [0, 1]).flatten

@[expose] def v0 : ℕ := 5

@[expose] def f0 : List ℕ := [0, v0, mvN z12 v0, mvN z12 (mvN z12 v0)]

@[expose] def orbL : List (ℕ × List ℕ) :=
  (H13.M22Cert.orbBfs gG 100 ((∅ : Std.HashSet ℕ).insert v0) [(v0, [])] [(v0, [])]).reverse

@[expose] def zB : Bool :=
  z12.length == 12 && tW zW == z12 && (gG.all fun g => mulN z12 g == mulN g z12) &&
    mulN z12 (mulN z12 z12) == one12 && z12 != one12 &&
    ((List.range 4096).all fun v => mvN z12 v != v || v == 0) && f0 == [0, 5, 10, 15]

@[expose] def orbB : Bool :=
  orbL.head? == some (v0, []) && orbL.length == 693 &&
    decide (((orbL.map Prod.fst).mergeSort).IsChain (· < ·)) &&
    orbL.all fun uw => mvN (tW uw.2) v0 == uw.1

@[expose] def s0W : List (List ℕ) :=
  [[0],
    [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]]

@[expose] def s0G : List (List ℕ) := s0W.map tW

@[expose] def s0E : List (List ℕ) := elemsOf 12 s0G

@[expose] def s0B : Bool :=
  subB 12 s0G s0E && s0E.length == 1920 && s0E.all fun s => mvN s v0 == v0

@[expose] def schB : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList s0E
  orbL.all fun uw => gG.all fun g =>
    match orbL.find? (fun p => p.1 == mvN g uw.1) with
    | some uw' =>
      let s := mulN (evalW 12 gInv uw'.2.reverse) (mulN g (tW uw.2))
      hs.contains s && mulN (tW uw'.2) s == mulN g (tW uw.2)
    | none => false

@[expose] def tG : List (List ℕ) :=
  [[1912, 2460, 1917, 2454, 2195, 3297, 3201, 1218, 29, 38, 351, 677],
    [1484, 2628, 1481, 2638, 1332, 2584, 2705, 4066, 382, 663, 2955, 3533],
    [1475, 2625, 1478, 2635, 1060, 2104, 2465, 3826, 97, 178, 2235, 3293]]

@[expose] def tE : List (List ℕ) := elemsOf 12 tG

@[expose] def tB : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList s0E
  subB 12 tG tE && tE.length == 128 && tG.all hs.contains &&
    (List.range 4096).all fun v => !(tG.all fun g => mvN g v == v) || f0.contains v

@[expose] def lineNe (a b : ℕ) : Bool := b != a && b != mvN z12 a && b != mvN z12 (mvN z12 a)

@[expose] def UC : List ℕ := [2725, 2720, 4080, 4090, 1375, 1360]

@[expose] def rP : List (List ℕ × List ℕ) :=
  [([1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
      [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]),
    ([2, 3, 7, 9, 109, 182, 65, 130, 971, 333, 3205, 1226],
      [3, 1, 6, 11, 251, 93, 67, 129, 589, 902, 2248, 3148]),
    ([3, 1, 6, 11, 251, 93, 67, 129, 589, 902, 2248, 3148],
      [2, 3, 7, 9, 109, 182, 65, 130, 971, 333, 3205, 1226]),
    ([112, 144, 117, 154, 726, 875, 447, 725, 3515, 1757, 4045, 1350],
      [224, 112, 229, 122, 2595, 3889, 1299, 2593, 3964, 1428, 762, 863]),
    ([144, 224, 149, 234, 587, 909, 463, 581, 2166, 3227, 2139, 3245],
      [159, 229, 154, 239, 3989, 1514, 2684, 3988, 1447, 2809, 1000, 380]),
    ([224, 112, 229, 122, 685, 1014, 351, 677, 2045, 2390, 1718, 3035],
      [117, 154, 112, 144, 1328, 2576, 3874, 1331, 2653, 4006, 351, 677]),
    ([384, 704, 389, 714, 971, 333, 162, 243, 381, 662, 2361, 3614],
      [398, 711, 395, 717, 560, 784, 894, 407, 406, 747, 3759, 2037]),
    ([385, 706, 388, 712, 134, 203, 534, 811, 800, 304, 4039, 1353],
      [394, 719, 399, 709, 109, 182, 752, 848, 731, 877, 2916, 3512]),
    ([386, 707, 391, 713, 971, 333, 55, 25, 731, 877, 1389, 2742],
      [386, 707, 391, 713, 971, 333, 55, 25, 731, 877, 1389, 2742]),
    ([704, 832, 709, 842, 800, 304, 290, 563, 560, 784, 2001, 2402],
      [704, 832, 709, 842, 800, 304, 290, 563, 560, 784, 2001, 2402]),
    ([706, 835, 711, 841, 16, 32, 919, 489, 678, 1019, 2464, 3824],
      [710, 843, 707, 833, 16, 32, 994, 371, 950, 475, 3487, 1765]),
    ([707, 833, 710, 843, 950, 475, 437, 730, 16, 32, 4039, 1353],
      [717, 838, 712, 844, 256, 512, 162, 243, 950, 475, 2709, 4074]),
    ([832, 384, 837, 394, 861, 422, 994, 371, 251, 93, 3205, 1226],
      [836, 392, 833, 386, 406, 747, 529, 802, 800, 304, 2361, 3614]),
    ([833, 386, 836, 392, 800, 304, 886, 411, 406, 747, 2129, 3234],
      [842, 399, 847, 389, 589, 902, 221, 102, 491, 637, 4021, 1498]),
    ([835, 385, 838, 395, 251, 93, 341, 682, 491, 637, 1724, 3028],
      [835, 385, 838, 395, 251, 93, 341, 682, 491, 637, 1724, 3028])]

@[expose] def y0W : List ℕ := [1, 0, 1, 1, 1]

@[expose] def y0 : List ℕ := tW y0W

@[expose] def rG : List (List ℕ) := tG ++ [z12, y0]

@[expose] def rE : List (List ℕ) := elemsOf 12 rG

end CFSG.Quasithin.H.Mathieu.H12Cert
