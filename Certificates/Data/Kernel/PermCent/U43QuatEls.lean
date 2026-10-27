module

public import Certificates.Data.Kernel.PermCent.U43QuatW
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Data1

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43.Quat

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def gamK : List ℕ :=
  [22908173855782, 45784966415719, 68661758713216, 137292136288051, 45784966028581,
    22908173521140]

@[expose] def quatEls : List (ℕ × Bool) :=
  [(1235367713451450, false), (411785751150849, false), (137354898085743, false),
    (617683856755249, false), (617683856676543, false), (cM1, false), (cC0, false),
    (848452467420, false)] ++ gamK.map (·, false)

@[expose] def quatElDets : List ℕ := [3, 3, 3, 3, 3, 6, 3, 3, 3, 3, 3, 3, 3, 3]

@[expose] def quatArrs : Array (Array ℕ) :=
  (quatEls.map fun x => tuL x.1 x.2).toArray ++ #[tuL cC0inv false, deltaArr, phiArr]

end CFSG.ComponentClassification.HarrisLit.P1.U43.Quat

end
