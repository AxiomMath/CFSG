module

public import Certificates.Data.K426J3

@[expose] public section

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier

namespace Certificates

@[expose] def j3fix (g : Array ℕ) : ℕ := (List.range 6156).countP fun p => g[p]! == p

@[expose] def j3e27Elt (m : ℕ) : Array ℕ :=
  compA 6156 (compA 6156 (powArr 6156 j3tLines[2]! (m / 9)) (powArr 6156 j3tLines[4]! (m / 3 % 3)))
    (powArr 6156 j3tLines[0]! (m % 3))

end Certificates

public section

namespace Certificates

end Certificates
