module

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

@[expose] def syl3CartanArr : Array Int :=
  #[2, 0, -1, 0, 0, 0, 0, 2, 0, -1, 0, 0, -1, 0, 2, -1, 0, 0, 0, -1, -1, 2, -1, 0, 0, 0, 0, -1, 2, -1,
    0, 0, 0, 0, -1, 2]

@[expose] def syl3ReflArr (k : Nat) : Array Int :=
  Array.ofFn fun e : Fin 36 =>
    (if e.val / 6 = e.val % 6 then 1 else 0) -
      (if e.val / 6 = k then syl3CartanArr.getD (6 * k + e.val % 6) 0 else 0)

@[expose] def syl3OneArr : Array Int :=
  Array.ofFn fun e : Fin 36 => if e.val / 6 = e.val % 6 then 1 else 0

@[expose] def syl3MulArr (a b : Array Int) : Array Int :=
  Array.ofFn fun e : Fin 36 =>
    a.getD (6 * (e.val / 6) + 0) 0 * b.getD (6 * 0 + e.val % 6) 0 +
      a.getD (6 * (e.val / 6) + 1) 0 * b.getD (6 * 1 + e.val % 6) 0 +
      a.getD (6 * (e.val / 6) + 2) 0 * b.getD (6 * 2 + e.val % 6) 0 +
      a.getD (6 * (e.val / 6) + 3) 0 * b.getD (6 * 3 + e.val % 6) 0 +
      a.getD (6 * (e.val / 6) + 4) 0 * b.getD (6 * 4 + e.val % 6) 0 +
      a.getD (6 * (e.val / 6) + 5) 0 * b.getD (6 * 5 + e.val % 6) 0

@[expose] def syl3Digit (ch : Char) : Int :=
  (ch.toNat : Int) - 100

@[expose] def syl3ArrOfChars (s : Array Char) (i : Nat) : Array Int :=
  Array.ofFn fun e : Fin 36 => syl3Digit (s.getD (36 * i + e.val) 'd')

@[expose] def syl3Tabulate {α : Type} {n : Nat} (f : Fin n → α) : Array α :=
  ((List.finRange n).map f).toArray

@[expose] def syl3SimpleWordData : List (List (Fin 6)) :=
  [
    [0, 2], [2, 0], [0, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 0, 3], [3, 0, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 0]
  ]

@[expose] def syl3SimpleWord (k : Fin 4) : List (Fin 6) :=
  syl3SimpleWordData.getD k.val []

@[expose] def syl3Inv (k : Fin 4) : Fin 4 :=
  [1, 0, 3, 2].getD k.val 0

@[expose] def syl3GenMatStr : String :=
  "ddcedddeddddedcedddddeddddddeddddddecdeddddeddddcddedddddeddddddedddddde" ++
    "dcddeddddceedddcfddddbgdddebfdcdecedddececcdfcddddfbedddgbddddfcdddeecdd"

@[expose] def syl3GenArr : Array (Array Int) :=
  let s := syl3GenMatStr.toList.toArray
  syl3Tabulate fun k : Fin 4 => syl3ArrOfChars s k.val

@[expose] def syl3GenWordData : List (List (Fin 4)) :=
  [
    [], [0], [1], [2], [3], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0], [2, 1], [3, 0], [3, 1], [0, 2, 0],
    [0, 2, 1], [0, 3, 0], [0, 3, 1], [1, 2, 0], [1, 2, 1], [1, 3, 0], [1, 3, 1], [2, 0, 2], [2, 0, 3],
    [2, 1, 2], [2, 1, 3], [3, 0, 2], [3, 0, 3], [3, 1, 2], [3, 1, 3], [0, 2, 0, 2], [0, 2, 0, 3],
    [0, 2, 1, 2], [0, 2, 1, 3], [0, 3, 0, 2], [0, 3, 0, 3], [0, 3, 1, 2], [0, 3, 1, 3], [1, 2, 0, 2],
    [1, 2, 0, 3], [1, 2, 1, 2], [1, 2, 1, 3], [1, 3, 0, 2], [1, 3, 0, 3], [1, 3, 1, 2], [1, 3, 1, 3],
    [2, 0, 2, 0], [2, 0, 2, 1], [2, 1, 2, 0], [2, 1, 2, 1], [3, 0, 3, 0], [3, 0, 3, 1], [3, 1, 3, 0],
    [3, 1, 3, 1], [0, 2, 0, 2, 0], [0, 2, 0, 2, 1], [0, 2, 1, 2, 0], [0, 2, 1, 2, 1], [0, 3, 0, 3, 0],
    [0, 3, 0, 3, 1], [0, 3, 1, 3, 0], [0, 3, 1, 3, 1], [1, 2, 0, 2, 0], [1, 2, 0, 2, 1], [1, 2, 1, 2, 0],
    [1, 2, 1, 2, 1], [1, 3, 0, 3, 0], [1, 3, 0, 3, 1], [1, 3, 1, 3, 0], [1, 3, 1, 3, 1], [2, 0, 2, 0, 2],
    [2, 0, 2, 1, 2], [2, 1, 2, 0, 2], [2, 1, 2, 1, 2], [0, 2, 0, 2, 0, 2], [0, 2, 0, 2, 1, 2],
    [0, 2, 1, 2, 0, 2], [0, 2, 1, 2, 1, 2], [1, 2, 0, 2, 0, 2], [1, 2, 0, 2, 1, 2], [1, 2, 1, 2, 0, 2],
    [1, 2, 1, 2, 1, 2]
  ]

@[expose] def syl3GenWord (i : Fin 81) : List (Fin 4) :=
  syl3GenWordData.getD i.val []

@[expose] def syl3MatStr : String :=
  "eddddddeddddddeddddddeddddddeddddddeddcedddeddddedcedddddeddddddeddddddecdeddddeddddcddedddddeddddddedddddde" ++
    "dcddeddddceedddcfddddbgdddebfdcdecedddececcdfcddddfbedddgbddddfcdddeecdddddceddddceedcdcfddddbgdddebfdcdeced" ++
    "ddedcdcdfcddddfcdcddgbddddfcdddeecdddedceddddceededbfddddbgdddebfdcdecedddecdecdfcddddfcceddgbddddfcdddeecdd" ++
    "dcddeddddceedddcfddddbgdedccfdeddceddcddeddddceedddcfddddbgdcddcfdddcdededcdecfdcdddfdbdedgdaeddfdbeddeecddd" ++
    "cdddeccdceddbdddedaddeddbddeddcedddddddceddddceedcdcfddddbgdedccfdeddceddddceddddceedcdcfddddbgdcddcfdddcded" ++
    "edcecdfdcdddfdbedcgdaeddfdbeddeecdddcddecdcdceddbddedcaddeddbddeddcedddddedceddddceededbfddddbgdedccfdeddced" ++
    "dedceddddceededbfddddbgdcddcfdddcdededcddefdcdddfdbecegdaeddfdbeddeecdddcddddecdceddbddeceaddeddbddeddcedddd" ++
    "ddececcdfcddddfbedddgbdddcfcdddcedddeddddddeddddddeddddddedddddedcddddecddececcdfcddddfbedddgbdddefbddddecdd" ++
    "eddddddeddddddeddddddedddddecedddecdecdddddbdedddbeddddadedddbddeddcdddedcdedcddddebdddedbdddedaddeddbcdeddc" ++
    "eedcdddedcdddfebdddgdbdddfdbeddedcdedcdecedddebedddebfdddeagddedbfcdedceddedcdcdfcddddfcdcddgbdddcfcdddceddd" ++
    "ddcedddeddddedcedddddedddddedcddddecddedcdcdfcddddfcdcddgbdddefbddddecddddcedddeddddedcedddddedddddecedddecd" ++
    "dccedddbdeddebcedddadedddbddeddcdddedddddcddddebdcdedbdddedaddeddbcdeddcdecddddedcddefccdddgdbdddfdbeddedcde" ++
    "ddddcedddebedcdebfdddeagddedbfcdedceddecdecdfcddddfcceddgbdddcfcdddcedddcdeddddeddddcddedddddedddddedcddddec" ++
    "ddecdecdfcddddfcceddgbdddefbddddecddcdeddddeddddcddedddddedddddecedddecdcceddddbdeddcbdedddadedddbddeddcddde" ++
    "dedddcddddebdedddbdddedaddeddbcdeddcceecdddedcddcfdcdddgdbdddfdbeddedcdededdcedddebededdbfdddeagddedbfcdedce" ++
    "edcdecfdcdddfdbdedgdaeddfcbeddecceddcdddeccdceddbdddedaddeddbcdeddccdeddedcdecfdcdddfdbdedgdaeddfebdddedcddd" ++
    "cdddeccdceddbdddedaddeddbeddddcddddddcdedcddddebdddedbdddedaedcedbeddddcdcdedcddddebdddedbdddedacddedbddcedc" ++
    "dcdecedddebedddebfdddeagedcebfedddcedcdecedddebedddebfdddeagcddebfddceceedcecdfdcdddfdbedcgdaeddfcbeddeccedd" ++
    "cddecdcdceddbddedcaddeddbcdeddccdeddedcecdfdcdddfdbedcgdaeddfebdddedcdddcddecdcdceddbddedcaddeddbeddddcddddd" ++
    "dddddcddddebdcdedbdddedaedcedbeddddcdddddcddddebdcdedbdddedacddedbddcedcddddcedddebedcdebfdddeagedcebfedddce" ++
    "ddddcedddebedcdebfdddeagcddebfddceceedcddefdcdddfdbecegdaeddfcbeddecceddcddddecdceddbddeceaddeddbcdeddccdedd" ++
    "edcddefdcdddfdbecegdaeddfebdddedcdddcddddecdceddbddeceaddeddbeddddcddddddedddcddddebdedddbdddedaedcedbeddddc" ++
    "dedddcddddebdedddbdddedacddedbddcedcdeddcedddebededdbfdddeagedcebfedddcededdcedddebededdbfdddeagcddebfddcece" ++
    "ecdddddbdedddbeddddadedddbdedcdcddeceedcdddedcdddfebdddgdbdddfdcdcdedcececdddddbdedddbeddddadedddbdecedcdecd" ++
    "eedcdddedcdddfebdddgdbdddfdccededdcddccedddbdeddebcedddadedddbdedcdcddecdecddddedcddefccdddgdbdddfdcdcdedcec" ++
    "dccedddbdeddebcedddadedddbdecedcdecddecddddedcddefccdddgdbdddfdccededdcdcceddddbdeddcbdedddadedddbdedcdcddec" ++
    "ceecdddedcddcfdcdddgdbdddfdcdcdedceccceddddbdeddcbdedddadedddbdecedcdecdceecdddedcddcfdcdddgdbdddfdccededdcd"

@[expose] def syl3MatsArr : Array (Array Int) :=
  let s := syl3MatStr.toList.toArray
  syl3Tabulate fun i : Fin 81 => syl3ArrOfChars s i.val

@[expose] def syl3TabData : List (List (Fin 81)) :=
  [
    [1, 2, 3, 4], [2, 0, 5, 6], [0, 1, 7, 8], [9, 10, 4, 0], [11, 12, 0, 3], [13, 14, 6, 1], [15, 16, 1, 5],
    [17, 18, 8, 2], [19, 20, 2, 7], [10, 3, 21, 22], [3, 9, 23, 24], [12, 4, 25, 26], [4, 11, 27, 28],
    [14, 5, 29, 30], [5, 13, 31, 32], [16, 6, 33, 34], [6, 15, 35, 36], [18, 7, 37, 38], [7, 17, 39, 40],
    [20, 8, 41, 42], [8, 19, 43, 44], [45, 46, 22, 9], [30, 38, 9, 21], [47, 48, 24, 10], [32, 40, 10, 23],
    [33, 41, 26, 11], [49, 50, 11, 25], [35, 43, 28, 12], [51, 52, 12, 27], [53, 54, 30, 13],
    [38, 22, 13, 29], [55, 56, 32, 14], [40, 24, 14, 31], [41, 25, 34, 15], [57, 58, 15, 33],
    [43, 27, 36, 16], [59, 60, 16, 35], [61, 62, 38, 17], [22, 30, 17, 37], [63, 64, 40, 18],
    [24, 32, 18, 39], [25, 33, 42, 19], [65, 66, 19, 41], [27, 35, 44, 20], [67, 68, 20, 43],
    [46, 21, 69, 49], [21, 45, 70, 51], [48, 23, 71, 50], [23, 47, 72, 52], [50, 26, 45, 69],
    [26, 49, 47, 71], [52, 28, 46, 70], [28, 51, 48, 72], [54, 29, 73, 57], [29, 53, 74, 59],
    [56, 31, 75, 58], [31, 55, 76, 60], [58, 34, 53, 73], [34, 57, 55, 75], [60, 36, 54, 74],
    [36, 59, 56, 76], [62, 37, 77, 65], [37, 61, 78, 67], [64, 39, 79, 66], [39, 63, 80, 68],
    [66, 42, 61, 77], [42, 65, 63, 79], [68, 44, 62, 78], [44, 67, 64, 80], [73, 77, 49, 45],
    [74, 78, 51, 46], [75, 79, 50, 47], [76, 80, 52, 48], [77, 69, 57, 53], [78, 70, 59, 54],
    [79, 71, 58, 55], [80, 72, 60, 56], [69, 73, 65, 61], [70, 74, 67, 62], [71, 75, 66, 63],
    [72, 76, 68, 64]
  ]

@[expose] def syl3TabArr : Array (Fin 81) :=
  ((List.finRange 81).flatMap fun i => (List.finRange 4).map fun k =>
    (syl3TabData.getD i.val []).getD k.val 0).toArray

@[expose] def syl3GenWordArr : Array (List (Fin 4)) :=
  syl3Tabulate syl3GenWord

@[expose] def syl3TabW (tab : Array (Fin 81)) (i : Fin 81) (k : Fin 4) : Fin 81 :=
  tab.getD (4 * i.val + k.val) 0

@[expose] def syl3Tab (i : Fin 81) (k : Fin 4) : Fin 81 :=
  syl3TabW syl3TabArr i k

@[expose] def syl3MulIdxW (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (i j : Fin 81) : Fin 81 :=
  (words.getD j.val []).foldl (fun m k => syl3TabW tab m k) i

@[expose] def syl3MulIdx (i j : Fin 81) : Fin 81 :=
  syl3MulIdxW syl3TabArr syl3GenWordArr i j

@[expose] def syl3PowIdxW (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (i : Fin 81) (a : Fin 3) :
    Fin 81 :=
  if a.val = 0 then 0 else if a.val = 1 then i else syl3MulIdxW tab words i i

@[expose] def syl3VecArr (n : Nat) : Array Int :=
  #[((n % 3 : Nat) : Int), ((n / 3 % 3 : Nat) : Int), ((n / 9 % 3 : Nat) : Int), ((n / 27 % 3 : Nat) : Int),
    ((n / 81 % 3 : Nat) : Int), ((n / 243 % 3 : Nat) : Int)]

@[expose] def syl3FixArr (a x : Array Int) : Bool :=
  (List.range 6).all fun c =>
    decide ((x.getD 0 0 * a.getD (6 * 0 + c) 0 + x.getD 1 0 * a.getD (6 * 1 + c) 0 +
      x.getD 2 0 * a.getD (6 * 2 + c) 0 + x.getD 3 0 * a.getD (6 * 3 + c) 0 +
      x.getD 4 0 * a.getD (6 * 4 + c) 0 + x.getD 5 0 * a.getD (6 * 5 + c) 0 - x.getD c 0) % 3 = 0)

@[expose] def syl3FixCodesW (mats : Array (Array Int)) : Array (List Nat) :=
  syl3Tabulate fun i : Fin 81 =>
    (List.range 729).filter fun n => syl3FixArr (mats.getD i.val #[]) (syl3VecArr n)

@[expose] def syl3Ord3W (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (i : Fin 81) : Bool :=
  decide (i ≠ 0) && decide (syl3MulIdxW tab words (syl3MulIdxW tab words i i) i = 0)

@[expose] def syl3CommW (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (i j : Fin 81) : Bool :=
  decide (syl3MulIdxW tab words i j = syl3MulIdxW tab words j i)

@[expose] def syl3IndepW (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (i j : Fin 81) : Bool :=
  decide (j ≠ 0) && decide (j ≠ i) && decide (j ≠ syl3MulIdxW tab words i i)

@[expose] def syl3OutW (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (i j k : Fin 81) : Bool :=
  (List.finRange 3).all fun a => (List.finRange 3).all fun b =>
    decide (k ≠ syl3MulIdxW tab words (syl3PowIdxW tab words i a) (syl3PowIdxW tab words j b))

@[expose] def syl3CheckGen (gens : Array (Array Int)) : Bool :=
  (List.finRange 4).all fun k =>
    decide (gens.getD k.val #[] =
      (syl3SimpleWord k).foldr (fun s M => syl3MulArr (syl3ReflArr s.val) M) syl3OneArr)

@[expose] def syl3CheckElt (gens mats : Array (Array Int)) (words : Array (List (Fin 4))) : Bool :=
  (List.finRange 81).all fun i =>
    decide (mats.getD i.val #[] =
      (words.getD i.val []).foldr (fun k M => syl3MulArr (gens.getD k.val #[]) M) syl3OneArr)

@[expose] def syl3CheckTab (gens mats : Array (Array Int)) (tab : Array (Fin 81)) : Bool :=
  (List.finRange 81).all fun i => (List.finRange 4).all fun k =>
    decide (syl3MulArr (mats.getD i.val #[]) (gens.getD k.val #[]) = mats.getD (syl3TabW tab i k).val #[])

@[expose] def syl3CheckInv (gens : Array (Array Int)) : Bool :=
  (List.finRange 4).all fun k =>
    decide (syl3MulArr (gens.getD k.val #[]) (gens.getD (syl3Inv k).val #[]) = syl3OneArr)

@[expose] def syl3CheckDistinct (mats : Array (Array Int)) : Bool :=
  (List.finRange 81).all fun i => (List.finRange 81).all fun j =>
    decide (i = j) ||
      (List.range 36).any fun e => decide ((mats.getD i.val #[]).getD e 0 ≠ (mats.getD j.val #[]).getD e 0)

@[expose] def syl3CheckNonab (tab : Array (Fin 81)) (words : Array (List (Fin 4))) : Bool :=
  (List.finRange 81).any fun i => (List.finRange 81).any fun j => !syl3CommW tab words i j

@[expose] def syl3CheckP1 (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (mats : Array (Array Int))
    (fix : Array (List Nat)) : Bool :=
  (List.finRange 81).all fun i => !syl3Ord3W tab words i || (List.finRange 81).all fun j =>
    !(syl3Ord3W tab words j && syl3CommW tab words i j && syl3IndepW tab words i j) ||
      decide (((fix.getD i.val []).filter fun n => syl3FixArr (mats.getD j.val #[]) (syl3VecArr n)).length ≤ 9)

@[expose] def syl3CheckP2 (tab : Array (Fin 81)) (words : Array (List (Fin 4))) (mats : Array (Array Int))
    (fix : Array (List Nat)) : Bool :=
  (List.finRange 81).all fun i => !syl3Ord3W tab words i || (List.finRange 81).all fun j =>
    !(syl3Ord3W tab words j && syl3CommW tab words i j && syl3IndepW tab words i j) ||
      (let F := (fix.getD i.val []).filter fun n => syl3FixArr (mats.getD j.val #[]) (syl3VecArr n)
       (List.finRange 81).all fun k =>
        !(syl3Ord3W tab words k && syl3CommW tab words i k && syl3CommW tab words j k &&
            syl3OutW tab words i j k) ||
          decide ((F.filter fun n => syl3FixArr (mats.getD k.val #[]) (syl3VecArr n)).length ≤ 3))

@[expose] def syl3Check (_ : Unit := ()) : Bool :=
  let gens := syl3GenArr
  let mats := syl3MatsArr
  let tab := syl3TabArr
  let words := syl3GenWordArr
  let fix := syl3FixCodesW mats
  syl3CheckGen gens && syl3CheckElt gens mats words && syl3CheckTab gens mats tab &&
    syl3CheckInv gens && syl3CheckDistinct mats && syl3CheckNonab tab words &&
    syl3CheckP1 tab words mats fix && syl3CheckP2 tab words mats fix

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

end
