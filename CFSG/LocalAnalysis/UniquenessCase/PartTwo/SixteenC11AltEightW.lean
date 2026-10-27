module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltCrit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16C11AltEightW

@[expose] def w1 : ↥(alternatingGroup (Fin 8)) := S16C11AltSw2 0 1 2 3 (by decide) (by decide)

@[expose] def w2 : ↥(alternatingGroup (Fin 8)) := S16C11AltSw2 0 2 1 3 (by decide) (by decide)

@[expose] def w3 : ↥(alternatingGroup (Fin 8)) := S16C11AltSw2 0 1 4 5 (by decide) (by decide)

@[expose] def w4 : ↥(alternatingGroup (Fin 8)) := S16C11AltSw2 4 5 6 7 (by decide) (by decide)

@[expose] def w5 : ↥(alternatingGroup (Fin 8)) := S16C11AltSw2 4 6 5 7 (by decide) (by decide)

@[expose] def w6 : ↥(alternatingGroup (Fin 8)) :=
  S16C11AltSw2 0 4 1 5 (by decide) (by decide) * S16C11AltSw2 2 6 3 7 (by decide) (by decide)

@[expose] def wordsL : List ↥(alternatingGroup (Fin 8)) :=
  [1, w1, w2, w3, w4, w5, w6, w1 * w2, w1 * w3, w1 * w4, w1 * w5, w1 * w6, w2 * w3,
    w2 * w4, w2 * w5, w2 * w6, w3 * w2, w3 * w4, w3 * w5, w3 * w6, w4 * w5, w4 * w6,
    w5 * w3, w5 * w6, w1 * w2 * w4, w1 * w2 * w5, w1 * w2 * w6, w1 * w3 * w4,
    w1 * w3 * w5, w1 * w3 * w6, w1 * w4 * w5, w1 * w4 * w6, w1 * w5 * w3,
    w1 * w5 * w6, w2 * w3 * w4, w2 * w3 * w5, w2 * w3 * w6, w2 * w4 * w5,
    w2 * w4 * w6, w2 * w5 * w3, w2 * w5 * w6, w3 * w2 * w4, w3 * w2 * w5,
    w3 * w2 * w6, w3 * w4 * w6, w3 * w5 * w6, w4 * w5 * w6, w5 * w3 * w2,
    w5 * w3 * w6, w1 * w2 * w4 * w5, w1 * w2 * w4 * w6, w1 * w2 * w5 * w6,
    w1 * w3 * w4 * w6, w1 * w3 * w5 * w6, w1 * w4 * w5 * w6, w1 * w5 * w3 * w6,
    w2 * w3 * w4 * w6, w2 * w3 * w5 * w6, w2 * w4 * w5 * w6, w2 * w5 * w3 * w6,
    w3 * w2 * w4 * w6, w3 * w2 * w5 * w6, w5 * w3 * w2 * w6, w1 * w2 * w4 * w5 * w6]

theorem wordsL_nodup : wordsL.Nodup := by decide +kernel

@[expose] def wordsT : Finset ↥(alternatingGroup (Fin 8)) := ⟨↑wordsL, wordsL_nodup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16C11AltEightW
