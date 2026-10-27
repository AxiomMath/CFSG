module

public import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.Recognition.McLCentralizer

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def mooreWord : ℕ → List ℕ
  | 1 => [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]
  | 2 => [0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]
  | 3 => [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]
  | 4 => [1, 1, 1, 1, 1, 0, 1, 0, 1]
  | 5 => [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  | 6 => [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1]
  | _ => []

@[expose] def mooreTab (i : ℕ) : Tab := wordTabS 35 mclXGens (mooreWord i)

@[expose] def sqTab (n : ℕ) (t : Tab) : Tab := comp n t t

@[expose] def cubeTab (n : ℕ) (t : Tab) : Tab := comp n t (comp n t t)

@[expose] def mooreCheck : Bool :=
  cubeTab 35 (mooreTab 1) == idTab 35 &&
    (List.range' 2 5).all (fun j => sqTab 35 (mooreTab j) == idTab 35 &&
      cubeTab 35 (comp 35 (mooreTab (j - 1)) (mooreTab j)) == idTab 35) &&
    (List.range' 1 4).all (fun i => (List.range' (i + 2) (5 - i)).all fun j =>
      sqTab 35 (comp 35 (mooreTab i) (mooreTab j)) == idTab 35)

@[expose] def mclCTabs : Array Tab := Array.ofFn (n := 2) fun k => natArr (mclCentTbl (k.val + 5))

@[expose] def liftTab : Tab := wordTabS 275 mclCTabs (mooreWord 4)

@[expose] def liftCheck : Bool := comp 275 liftTab liftTab == mclT0Arr

end CFSG.Sporadic.Recognition.McLCentralizer
