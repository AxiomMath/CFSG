module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE8
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration Polynomial

namespace NoOffE8Five

@[expose] def e8WMat : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 0, 2], [-1, 0, -1, 1, -1, 1, -1, 3], [-2, 1, 0, 0, -1, 1, -1, 4],
   [-3, 0, 0, 1, -2, 2, -2, 6], [-3, 0, 0, 1, -1, 1, -2, 5], [-2, 0, 0, 0, 0, 1, -2, 4],
   [-2, 0, 0, 0, 0, 1, -1, 2], [-1, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8WBasis : List (List ℤ) :=
  [[1, -1, 0, 0, 0, 0, 0, 0], [0, -1, 1, 0, 0, 1, 0, 1], [0, -2, 0, 1, 0, 0, 0, 1],
   [0, -3, 0, 0, 1, 1, 0, 2], [0, -3, 0, 0, 0, 1, 0, 1], [0, -2, 0, 0, 0, 0, 1, 1],
   [0, -2, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 0, 0, 0, 0]]

@[expose] def e8WBasisInv : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, -1, 0, 0, 2],
   [0, 0, 1, 0, 0, 0, -1, 0], [0, 0, 0, 1, -1, 0, -1, 2], [0, 0, 0, 0, 1, 0, -1, -1],
   [0, 0, 0, 0, 0, 1, -1, 0], [0, 0, 0, 0, 0, 0, 1, -2]]

theorem e8W_wordMat :
    wordMat Tag.E8 NoOffRest.wordE8W = toMat Tag.E8.rank e8WMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8W_pow : (wordMat Tag.E8 NoOffRest.wordE8W) ^ 4 = 1 := by
  rw [e8W_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8W_charpoly :
    (wordMat Tag.E8 NoOffRest.wordE8W).charpoly =
      ([4, 4, 4, 4].map fun d => cyclotomic d ℤ).prod := by
  rw [e8W_wordMat]
  exact charpoly_of_basis e8WMat e8WBasis e8WBasisInv [4, 4, 4, 4]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

end NoOffE8Five

end CFSG.StandardType
