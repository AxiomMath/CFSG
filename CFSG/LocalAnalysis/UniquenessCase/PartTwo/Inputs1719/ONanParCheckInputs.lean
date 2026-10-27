module

public import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
public import CFSG.Sporadic.ONOddCore.SylowEightCheckInputs
public meta import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
public meta import CFSG.Sporadic.ONOddCore.SylowEightCheckInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore
open CFSG.Sporadic.ON.Native (nPts)

@[expose] def onpVWord : List Int := [-6, -4, -5, 1, 2, 3, 7, -3, 7, 3, 6, 7, 6]

@[expose] def onpXWord : List Int := [-2, -5, -7, 5, -6, 1, 3, -4, -6, -5, -5, -7, 6]

@[expose] def onpMWord : List Int := [4, 1, -3, 5, 1, -2, 5, 5, 4, 5, 3, 7, 6, -7, -6]

@[expose] def onpNWord : List Int := [5, -7, 1, -2, 1, -2, -5, -4, -7, 5, 6, -3, 6, 7]

@[expose] def onpV32 : Array Nat := #[
    0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 25, 26, 12, 13, 28, 15, 16, 18, 17, 20, 19, 21, 22, 31, 30, 10,
    11, 27, 14, 29, 24, 23]

@[expose] def onpVB : Array Nat := #[
    114, 33, 48, 110, 61, 50, 31, 93, 8, 112, 88, 65, 19, 79, 53, 102, 16, 90, 86, 12,
    44, 67, 22, 78, 99, 34, 42, 83, 98, 52, 77, 6, 104, 1, 25, 115, 89, 60, 105, 71,
    100, 64, 26, 47, 20, 107, 108, 43, 2, 116, 5, 72, 29, 14, 75, 69, 73, 94, 70, 59,
    37, 4, 101, 80, 41, 11, 82, 21, 81, 55, 58, 39, 51, 56, 74, 54, 117, 30, 23, 13,
    63, 68, 66, 27, 118, 95, 18, 113, 10, 36, 17, 91, 119, 7, 57, 85, 96, 97, 28, 24,
    40, 62, 15, 106, 32, 38, 103, 45, 46, 111, 3, 109, 9, 87, 0, 35, 49, 76, 84, 92]

@[expose] def onpVArr : Array Nat := wordArr onpVWord

@[expose] def onpXArr : Array Nat := wordArr onpXWord

@[expose] def onpMArr : Array Nat := wordArr onpMWord

@[expose] def onpNArr : Array Nat := wordArr onpNWord

@[expose] def onpGArr : Array Nat :=
  pcomp nPts onpNArr (pcomp nPts onpXArr (pcomp nPts onpMArr onpXArr))

@[expose] def onpOmInv : Array Tab := omegaEnum.tabs.map (invTab 32)

@[expose] def onpTInv : Array Tab := t32Enum.tabs.map (invTab 32)

@[expose] def onpCommGens : Array Tab :=
  Array.ofFn (n := omegaEnum.tabs.size * t32Enum.tabs.size) fun k =>
    commTab 32 omegaEnum.tabs[k.val / t32Enum.tabs.size]! t32Enum.tabs[k.val % t32Enum.tabs.size]!
      onpOmInv[k.val / t32Enum.tabs.size]! onpTInv[k.val % t32Enum.tabs.size]!

@[expose] def onpCommEnum : Enum := enumBFS 32 onpCommGens 16

@[expose] def onpRGens : Array Tab :=
  (wordArrs Data.MWords).map fun g =>
    conjTab 120 Data.quotientConjugator (pinvCand 120 Data.quotientConjugator) (bTab g)

@[expose] def onpRGensInv : Array Tab := onpRGens.map (invTab 120)

@[expose] def onpVBar : Tab :=
  conjTab 120 Data.quotientConjugator (pinvCand 120 Data.quotientConjugator) onpVB

@[expose] def onpROrbit : Enum := orbitBFS 120 onpRGens onpRGensInv onpVBar 400

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
