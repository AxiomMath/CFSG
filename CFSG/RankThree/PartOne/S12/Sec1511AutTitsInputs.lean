module

public import CFSG.RankThree.PartOne.K159.AutTitsInputs

public section

namespace CFSG.RankThree.PartOne.Sec1511

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
open CFSG.RankThree.PartOne.K159

@[expose] def titsHWord : List ℤ := [6, 7, 12, 3, -6, -5, -5, -13, -3, -3]

@[expose] def titsGInvWord : List ℤ := [8, -6, -6, -6, 9, -6, 5, -12, -2, -6, 11, 8, -2, -1]

@[expose] def titsRWord : ℕ → List ℤ
  | 0 => []
  | 1 => titsHWord
  | 2 => titsHWord ++ titsGWord
  | _ => titsHWord ++ titsGInvWord

@[expose] def titsBigWord (n : ℕ) : List ℤ :=
  (List.replicate (n / 4) titsGWord).flatten ++ titsRWord (n % 4)

@[expose] def titsBigData : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 1), (4, 0, 2, 1), (0, 4, 1, 4), (2, 4, 2, 2), (3, 4, 2, 4), (2, 1, 3, 2), (3, 1, 1, 0),
    (4, 4, 0, 1), (2, 3, 4, 4), (3, 2, 3, 0), (1, 1, 3, 4), (0, 2, 2, 4), (2, 0, 0, 2), (3, 0, 4, 2),
    (0, 3, 2, 3), (4, 3, 4, 4), (1, 3, 4, 3), (4, 2, 1, 4), (1, 2, 2, 0), (3, 3, 0, 2), (4, 1, 3, 3),
    (1, 4, 1, 0), (2, 2, 1, 3), (0, 4, 4, 3), (4, 0, 0, 4), (1, 0, 3, 4), (0, 1, 4, 1), (3, 1, 3, 3),
    (2, 1, 3, 1), (3, 4, 2, 3), (2, 4, 4, 0), (1, 1, 0, 4), (3, 2, 1, 1), (2, 3, 2, 0), (4, 4, 2, 1),
    (0, 3, 3, 1), (3, 0, 0, 3), (2, 0, 1, 3), (0, 2, 3, 2), (1, 2, 1, 1), (4, 2, 1, 2), (1, 3, 4, 1),
    (4, 3, 3, 0), (2, 2, 0, 3), (1, 4, 2, 2), (4, 1, 4, 0), (3, 3, 4, 2), (0, 1, 1, 2)]

@[expose] def titsBigDat (n : ℕ) : ℕ × ℕ × ℕ × ℕ := titsBigData.getD n (0, 0, 0, 0)

@[expose] def titsBigArr (n : ℕ) : Array ℕ := wordArr 1755 titsDerivedArrs (titsBigWord n)

@[expose] def titsBigOK (n : ℕ) : Bool :=
  lettersOK 13 (titsBigWord n) && decide ((titsBigDat n).1 < 5) && decide ((titsBigDat n).2.1 < 5) &&
    decide ((titsBigDat n).2.2.1 < 5) && decide ((titsBigDat n).2.2.2 < 5) &&
    eqA 1755 (compA 1755 (titsBigArr n) titsAArr)
      (compA 1755 (pairArr (titsBigDat n).1 (titsBigDat n).2.1) (titsBigArr n)) &&
    eqA 1755 (compA 1755 (titsBigArr n) titsBArr)
      (compA 1755 (pairArr (titsBigDat n).2.2.1 (titsBigDat n).2.2.2) (titsBigArr n))

@[expose] def TitsBigCheck : Prop :=
  titsBigData.length = 48 ∧ titsBigData.Nodup ∧ allLt 48 titsBigOK = true

instance : Decidable TitsBigCheck := by
  unfold TitsBigCheck
  infer_instance

end CFSG.RankThree.PartOne.Sec1511
