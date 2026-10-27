module

public import CFSG.RankThree.PartOne.SEITZQ1.F4Mat
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.SEITZQ1

@[expose] def q1SigPos : Bool → Fin 3 → Fin 3 → ℕ
  | false, 0, 1 => 7
  | false, 0, 2 => 35
  | false, 1, 0 => 14
  | false, 1, 2 => 22
  | false, 2, 0 => 38
  | false, 2, 1 => 29
  | true, 0, 1 => 42
  | true, 0, 2 => 0
  | true, 1, 0 => 39
  | true, 1, 2 => 43
  | true, 2, 0 => 4
  | true, 2, 1 => 46
  | _, _, _ => 0

@[expose] def q1TauPos : Bool → Bool → Fin 3 → Fin 3 → ℕ
  | false, false, 0, 1 => 16
  | false, false, 0, 2 => 36
  | false, false, 1, 0 => 26
  | false, false, 1, 2 => 17
  | false, false, 2, 0 => 41
  | false, false, 2, 1 => 27
  | false, true, 0, 1 => 10
  | false, true, 0, 2 => 3
  | false, true, 1, 0 => 19
  | false, true, 1, 2 => 9
  | false, true, 2, 0 => 11
  | false, true, 2, 1 => 2
  | true, false, 0, 1 => 26
  | true, false, 0, 2 => 41
  | true, false, 1, 0 => 16
  | true, false, 1, 2 => 27
  | true, false, 2, 0 => 36
  | true, false, 2, 1 => 17
  | true, true, 0, 1 => 19
  | true, true, 0, 2 => 11
  | true, true, 1, 0 => 10
  | true, true, 1, 2 => 2
  | true, true, 2, 0 => 3
  | true, true, 2, 1 => 9
  | _, _, _, _ => 0

@[expose] def q1Coef (x : Fin 4) : ℤ := if x = 0 then 0 else 1

@[expose] def q1Pow (x : Fin 4) : ℕ := ![0, 0, 1, 2] x

@[expose] def q1Frob (odd : Bool) (x : Fin 4) : Fin 4 := if odd then f4Mul x x else x

@[expose] def q1DecWord (odd side : Bool) (l : List (Fin 3 × Fin 3 × Fin 4)) :
    List (ℕ × ℤ × ℕ) :=
  l.map (fun x => (q1SigPos side x.1 x.2.1, q1Coef x.2.2, q1Pow x.2.2)) ++
    l.map (fun x =>
      (q1TauPos odd side x.1 x.2.1, q1Coef (q1Frob odd x.2.2), q1Pow (q1Frob odd x.2.2)))

@[expose] def q1LetterWord (odd side : Bool) (k : Fin 9) : List (ℕ × ℤ × ℕ) :=
  q1DecWord odd side (q1LetterDec k)

@[expose] def q1CWord : List (ℕ × ℤ × ℕ) :=
  [(4, 1, 1), (0, 1, 0), (11, 1, 1), (3, 1, 0), (38, 1, 1), (35, 1, 0), (41, 1, 1), (36, 1, 0)]

@[expose] def q1Letters : Bool → List (Bool × Fin 9)
  | false => [(false, 0), (true, 1), (false, 4), (true, 2), (false, 1), (true, 5), (false, 8)]
  | true => [(false, 2), (true, 2), (false, 7), (true, 4), (false, 3), (true, 2), (false, 6)]

@[expose] def q1Full (odd tgt : Bool) : List (ℕ × ℤ × ℕ) :=
  q1CWord ++ (q1Letters tgt).flatMap (fun x => q1LetterWord odd x.1 x.2) ++ q1CWord.reverse

@[expose] def q1Target : Bool → List (ℕ × ℤ × ℕ)
  | false => [(1, 1, 0), (6, 1, 0), (1, 1, 0), (2, 1, 0), (9, 1, 0), (2, 1, 0), (1, 1, 0),
      (6, 1, 0), (1, 1, 0), (2, 1, 0), (9, 1, 0), (2, 1, 0)]
  | true => [(2, 1, 0), (1, 1, 0), (7, 1, 0)]

end CFSG.RankThree.PartOne.SEITZQ1
