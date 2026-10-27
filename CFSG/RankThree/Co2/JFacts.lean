module

public import CFSG.RankThree.Co2.SylFacts
public import CFSG.RankThree.Co2.CensusData

public section

namespace CFSG.RankThree.Co2

@[expose] def jMatN : ℕ → ℕ → Matrix (Fin 22) (Fin 22) (ZMod 2)
  | 0, _ => 1
  | n + 1, v => jMatN n v * (if v.testBit n then wordMat jWords[n]! else 1)

@[expose] def jMat (v : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) := jMatN 10 v

structure TFacts : Prop where
  pow : ∀ x ∈ matGrp sylWords, x ^ 32 = 1
  card : 2 ^ 18 ≤ Nat.card (matGrp sylWords)

structure JFacts : Prop where
  sq : ∀ i < 10, wordMat jWords[i]! * wordMat jWords[i]! = 1
  comm : ∀ i < 10, ∀ k < 10,
    wordMat jWords[i]! * wordMat jWords[k]! = wordMat jWords[k]! * wordMat jWords[i]!
  bij : Set.BijOn jMat (Set.Iio 1024) (matGrp jWords)
  le : matGrp jWords ≤ matGrp sylWords
  norm : ∀ t ∈ matGrp sylWords, ∀ x ∈ matGrp jWords, ∃ y ∈ matGrp jWords, t * x = y * t
  cent : Nat.card (matGrp sylWords) ≤ 2 ^ 18 →
    ∀ t ∈ matGrp sylWords, (∀ x ∈ matGrp jWords, t * x = x * t) → t ∈ matGrp jWords
  ea : Nat.card (matGrp sylWords) ≤ 2 ^ 18 →
    ∀ A : Set (Matrix (Fin 22) (Fin 22) (ZMod 2)), A ⊆ matGrp sylWords → 1 ∈ A →
      (∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (∀ x ∈ A, x * x = 1) → Nat.card A = 1024 → A = matGrp jWords

end CFSG.RankThree.Co2

end
