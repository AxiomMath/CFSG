module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs

@[expose] public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

def titsFiveWord : List ℤ := [3, 4, 13, 3, 4, 13]

def titsFiveArr : Array ℕ := wordArr 1755 titsDerivedArrs titsFiveWord

def titsCH5 : List (Array ℕ) :=
  survivors5 1755 titsHLevels fun a => commA a titsFiveArr

end CFSG.RankThree.PartOne.KE
