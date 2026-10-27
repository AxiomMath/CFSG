module

public import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public import Certificates.Certificate7074

public section

namespace CFSG.ASVolI.AppH

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def offPts24 : List ℕ := [8, 11, 13, 14, 17, 18, 20, 23]

@[expose] def fixesOff24 (s : T24s2.Elem) : Bool :=
  offPts24.all fun i => (T24s2.arr s)[i]! == i

@[expose] def predOff24 (l : List T24s2.Elem) : Bool :=
  let k := l.length
  let d := Nat.log 2 (fixMasks24 l).length
  decide (k ≤ 6) && (k == 0 || !decide (11 - d ≤ k + 1) || (k == 4 && l.all fixesOff24))

end CFSG.ASVolI.AppH
