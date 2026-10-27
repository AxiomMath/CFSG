module

public import CFSG.Quasithin.Background.HMathieuSyl22
public meta import CFSG.Quasithin.Background.HMathieuSyl22
public import Certificates.Certificate7068

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def offPts22 : List ℕ := [0, 1, 4, 7, 13, 15, 17, 19]

@[expose] def fixesOff22 (s : T22s2.Elem) : Bool :=
  offPts22.all fun i => (T22s2.arr s)[i]! == i

@[expose] def predOff22 (k : ℕ) (l : List T22s2.Elem) : Bool :=
  let d := Nat.log 2 (fixMasks 10 act22s2 l).length
  decide (k ≤ 5) && (!decide (10 - d ≤ k + 1) || (k == 4 && l.all fixesOff22))

end CFSG.ASVolI.AppH
