module

public import CFSG.RankThree.Co2.CrConj
public import CFSG.RankThree.Co2.ZuWordsData

public section

namespace CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def zuMatN : ℕ → ℕ → M22
  | 0, _ => 1
  | n + 1, m => zuMatN n m * (if m.testBit n then wordMat zuGenWords[n]! else 1)

@[expose] def zuMat (m : ℕ) : M22 := zuMatN 4 m

@[expose] def zuCls : Array ℕ := #[0, 0, 7, 8, 8, 7, 1, 1, 3, 2, 5, 6, 6, 5, 3, 2]

structure C4Facts : Prop where
  lam : ∀ y, (CrConj (repMat 2) y ∨ CrConj (repMat 7) y) → y * repMat 8 = repMat 8 * y →
    (y * repMat 8 = repMat 0 ∨ CrConj (repMat 2) (y * repMat 8) ∨
      CrConj (repMat 7) (y * repMat 8)) → y = repMat 7
  sq : ∀ k < 4, wordMat zuGenWords[k]! * wordMat zuGenWords[k]! = 1
  comm : ∀ k < 4, ∀ j < 4,
    wordMat zuGenWords[k]! * wordMat zuGenWords[j]! = wordMat zuGenWords[j]! * wordMat zuGenWords[k]!
  mem : ∀ m < 16, zuMat m ∈ matGrp pWords8 ∧ ∀ y ∈ matGrp pWords8, zuMat m * y = y * zuMat m
  all : Nat.card (matGrp pWords8) ≤ 2 ^ 14 → ∀ x ∈ matGrp pWords8,
    (∀ y ∈ matGrp pWords8, x * y = y * x) → ∃ m < 16, x = zuMat m
  cls : ∀ m, 0 < m → m < 16 → CrConj (repMat zuCls[m]!) (zuMat m)

end CFSG.RankThree.Co2

end
