module

public import CFSG.RankThree.Co2.X9CertInputs

public section

namespace CFSG.RankThree.Co2

structure X9Facts : Prop where
  comm9 : ∀ k : Fin xWords9.size, wordMat xWords9[k] * repMat 9 = repMat 9 * wordMat xWords9[k]
  card : 6144 ≤ Nat.card (matGrp xWords9)
  ne : wordMat dWord ≠ 1
  commD : ∀ k : Fin xWords9.size,
    wordMat xWords9[k] * wordMat dWord = wordMat dWord * wordMat xWords9[k]
  sq : ∃ y ∈ matGrp xWords9, y * y = wordMat dWord
  cen : Nat.card (matGrp xWords9) ≤ 6144 → ∀ y ∈ matGrp xWords9,
    (∀ x ∈ matGrp xWords9, x * (y * y) = y * y * x) → y * y = 1 ∨ y * y = wordMat dWord
  conj9 : CrConj (repMat 9) (repMat 9 * wordMat dWord)
  conj1 : CrConj (repMat 1) (repMat 0 * wordMat dWord)

end CFSG.RankThree.Co2

end
