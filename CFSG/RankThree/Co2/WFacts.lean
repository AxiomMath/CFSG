module

public import CFSG.RankThree.Co2.CrConj
public import CFSG.RankThree.Co2.WWordsData

public section

namespace CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def InA (x : M22) : Prop := ∃ c ∈ [0, 2, 7], CrConj (repMat c) x

@[expose] def InB (x : M22) : Prop := ∃ c ∈ [1, 3, 5], CrConj (repMat c) x

structure WFacts : Prop where
  comm : ∀ x ∈ matGrp wGenWords, ∀ y ∈ matGrp wGenWords, x * y = y * x
  sq : ∀ x ∈ matGrp wGenWords, x * x = 1
  card : Nat.card (matGrp wGenWords) = 32
  cases : ∀ x ∈ matGrp wGenWords, x = 1 ∨ x = repMat 1 ∨ (InA x ∧ InB (x * repMat 1)) ∨
    (InB x ∧ InA (x * repMat 1))
  card_typeAB : Nat.card {x : M22 // x ∈ matGrp wGenWords ∧ InA x ∧ InB (x * repMat 1)} = 15
  closed : ∀ x ∈ Cm, x * repMat 1 = repMat 1 * x →
    (InA x ∧ InB (x * repMat 1)) ∨ (InB x ∧ InA (x * repMat 1)) → x ∈ matGrp wGenWords
  le : matGrp wGenWords ≤ matGrp pWords1
  center : Nat.card (matGrp pWords1) ≤ 2 ^ 17 → ∀ x ∈ matGrp pWords1,
    (∀ y ∈ matGrp pWords1, x * y = y * x) →
      x = 1 ∨ x = repMat 1 ∨ x = repMat 0 ∨ x = repMat 0 * repMat 1
  cent : Nat.card (matGrp pWords1) ≤ 2 ^ 17 →
    Nat.card {x : M22 // x ∈ matGrp pWords1 ∧ ∀ w ∈ matGrp wGenWords, x * w = w * x} ≤ 2048
  odd3 : ∃ x ∈ Cm, x ^ 3 = 1 ∧ x * repMat 1 = repMat 1 * x ∧
    ∃ w ∈ matGrp wGenWords, w * x ≠ x * w
  odd7 : ∃ x ∈ Cm, x ^ 7 = 1 ∧ x * repMat 1 = repMat 1 * x ∧
    ∃ w ∈ matGrp wGenWords, w * x ≠ x * w

end CFSG.RankThree.Co2

end
