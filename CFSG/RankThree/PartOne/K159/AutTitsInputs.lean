module

public import CFSG.Sporadic.Schreier.TitsArrays
public import CFSG.Sporadic.Schreier.TitsBasic

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def titsAWord : List ℤ := [3, 4, 13, 3, 4, 13]

@[expose] def titsBWord : List ℤ :=
  [-10, -2, -1, -11, -4, 12, 1, -4, 3, 3, 11, -7, 3, 4, 13, 3, 4, 13, 7, -11, -3, -3, 4, -1, -12, 4,
    11, 1, 2, 10]

@[expose] def titsGWord : List ℤ := [1, 2, -8, -11, 6, 2, 12, -5, 6, -9, 6, 6, 6, -8]

@[expose] def titsAArr : Array ℕ := wordArr 1755 titsDerivedArrs titsAWord

@[expose] def titsBArr : Array ℕ := wordArr 1755 titsDerivedArrs titsBWord

@[expose] def titsGArr : Array ℕ := wordArr 1755 titsDerivedArrs titsGWord

@[expose] def powArr (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 1755
  | k + 1 => compA 1755 x (powArr x k)

@[expose] def pairArr (i j : ℕ) : Array ℕ := compA 1755 (powArr titsAArr i) (powArr titsBArr j)

@[expose] def TitsAutCheck : Prop :=
  lettersOK 13 titsAWord = true ∧ lettersOK 13 titsBWord = true ∧ lettersOK 13 titsGWord = true ∧
  eqA 1755 (powArr titsAArr 5) (idA 1755) = true ∧
  eqA 1755 (powArr titsBArr 5) (idA 1755) = true ∧
  eqA 1755 (compA 1755 titsAArr titsBArr) (compA 1755 titsBArr titsAArr) = true ∧
  allLt 5 (fun i => allLt 5 (fun j => allLt 5 (fun i' => allLt 5 (fun j' =>
    ((i == i') && (j == j')) || !(eqA 1755 (pairArr i j) (pairArr i' j')))))) = true ∧
  eqA 1755 (compA 1755 titsGArr titsAArr) (compA 1755 (pairArr 3 4) titsGArr) = true ∧
  eqA 1755 (compA 1755 titsGArr titsBArr) (compA 1755 (pairArr 2 4) titsGArr) = true ∧
  allLt 4 (fun k => !(eqA 1755 (compA 1755 (powArr titsGArr (k + 1)) titsAArr)
    (compA 1755 titsAArr (powArr titsGArr (k + 1))))) = true

instance : Decidable TitsAutCheck := by
  unfold TitsAutCheck
  infer_instance

end CFSG.RankThree.PartOne.K159
