module

public import CFSG.Quasithin.Background.H12OneHatM22PfInputs
public import Mathlib

public noncomputable section

namespace CFSG.KC.H12C

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert

@[expose] def tGW : List (List ℕ) :=
  [[3, 1, 2, 1, 2, 1, 3, 0], [1, 2, 1, 0, 3, 0, 2, 0], [3, 2, 1, 3, 1, 0, 3]]

@[expose] def rPW : List (List ℕ) :=
  [[], [3, 2, 3, 1, 2, 1, 2], [0, 2, 1, 0, 3, 1, 2, 0], [1, 3, 2, 3, 0, 3], [0, 2, 1, 2, 1, 3, 1],
    [2, 3, 3, 0, 2, 3, 1], [2, 0, 2, 0, 3, 2], [0, 3, 2, 3, 0, 2], [3, 1, 3, 1, 2, 3, 2],
    [2, 1, 2, 1, 0, 2], [1, 0, 3, 3, 1, 3, 0], [3, 0, 3, 1, 3, 1, 0], [1, 3, 0, 2, 1],
    [1, 0, 2, 0, 3, 3, 1], [3, 2, 1, 3, 2, 1]]

@[expose] def r0W : List (List ℕ) :=
  [[], [3], [4], [2, 4], [3, 3], [4, 3], [2, 4, 3], [4, 3, 3], [2, 4, 3, 3]]

@[expose] def r0P : List (List ℕ × List ℕ) :=
  [([1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
      [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]),
    ([2, 3, 8, 12, 32, 48, 128, 192, 512, 768, 2048, 3072],
      [3, 1, 12, 4, 48, 16, 192, 64, 768, 256, 3072, 1024]),
    ([2561, 3842, 164, 248, 64, 128, 16, 32, 3664, 1952, 2896, 3488],
      [2561, 3842, 164, 248, 64, 128, 16, 32, 3664, 1952, 2896, 3488]),
    ([2476, 3828, 780, 260, 2465, 3826, 1060, 2104, 2385, 3746, 395, 717],
      [4041, 1358, 1388, 2740, 478, 615, 1022, 343, 1380, 2744, 1867, 2445]),
    ([3, 1, 12, 4, 48, 16, 192, 64, 768, 256, 3072, 1024],
      [2, 3, 8, 12, 32, 48, 128, 192, 512, 768, 2048, 3072]),
    ([3842, 1283, 248, 92, 128, 192, 32, 48, 1952, 2544, 3488, 1776],
      [1283, 2561, 92, 164, 192, 64, 48, 16, 2544, 3664, 1776, 2896]),
    ([3828, 1880, 260, 520, 3826, 1875, 2104, 3100, 3746, 2035, 717, 838],
      [2695, 4041, 4056, 1388, 953, 478, 681, 1022, 4060, 1380, 3782, 1867]),
    ([1283, 2561, 92, 164, 192, 64, 48, 16, 2544, 3664, 1776, 2896],
      [3842, 1283, 248, 92, 128, 192, 32, 48, 1952, 2544, 3488, 1776]),
    ([1880, 2476, 520, 780, 1875, 2465, 3100, 1060, 2035, 2385, 838, 395],
      [1358, 2695, 2740, 4056, 615, 953, 343, 681, 2744, 4060, 2445, 3782])]

@[expose] def sA : List ℕ := [1360, 1375]

@[expose] def inT (x : List ℕ) : Bool := (Std.HashSet.ofList tE).contains x

@[expose] def wB : Bool :=
  tGW.map (evalW 12 s0G) == tG && rPW.map (evalW 12 s0G) == rP.map Prod.fst &&
    r0W.map (evalW 12 rG) == r0P.map Prod.fst && (s0G.all fun g => mvN g v0 == v0) &&
    tW zW == z12 && !(f0.contains (mvN y0 v0))

@[expose] def tB2 : Bool :=
  subB 12 tG tE && tE.length == 128 &&
    ((List.range 4096).all fun v => !(tG.all fun g => mvN g v == v) || f0.contains v) &&
    (tG.all fun g => sA.all fun a => sA.contains (mvN g a)) && tG.all fun g => mvN g 5 == 5

@[expose] def cosB (gens : List (List ℕ)) (reps : List (List ℕ × List ℕ)) (A : List ℕ) (a : ℕ) :
    Bool :=
  (reps.all fun r => validB 12 r.1 && validB 12 r.2 && mulN r.1 r.2 == one12) &&
    nodupB 12 (reps.map Prod.fst) && (reps.any fun r => inT r.1) &&
    (gens.all fun g => reps.all fun r => reps.any fun r' =>
      A.contains (mvN r'.2 (mvN g (mvN r.1 a))) && inT (mulN r'.2 (mulN g r.1))) &&
    reps.all fun r => reps.all fun r' => r.1 == r'.1 || !A.contains (mvN r'.2 (mvN r.1 a))

@[expose] def orbK : List (List (ℕ × List ℕ)) :=
  (List.range 64).map fun b => orbL.filter fun p => p.1 % 64 == b

@[expose] def inRT (s : List ℕ) : Bool :=
  rP.any fun r => sA.contains (mvN r.2 (mvN s 1360)) && inT (mulN r.2 s)

@[expose] def schE (g M : List ℕ) (y : ℕ) : Bool :=
  match ((orbK.getD (y % 64) []).find? fun p => p.1 == y) with
  | some uw' =>
    let s := mulN (evalW 12 gInv uw'.2.reverse) (mulN g M)
    mulN (tW uw'.2) s == mulN g M && inRT s
  | none => false

@[expose] def schC : Bool :=
  orbL.all fun uw => gG.all fun g => schE g (tW uw.2) (mvN g uw.1)

@[expose] def ball3 : List (List ℕ) :=
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]

@[expose] def ov1C : Bool :=
  orbL.all fun uw => f0.contains uw.1 || UC.contains uw.1 ||
    ball3.any fun w₁ => lineNe uw.1 (mvN (evalW 12 tG w₁) uw.1) &&
      ball3.any fun w₂ => lineNe uw.1 (mvN (evalW 12 tG w₂) uw.1) &&
        lineNe (mvN (evalW 12 tG w₁) uw.1) (mvN (evalW 12 tG w₂) uw.1)

end CFSG.KC.H12C

end
