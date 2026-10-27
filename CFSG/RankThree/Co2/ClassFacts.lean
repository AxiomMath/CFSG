module

public import CFSG.RankThree.Co2.CrConj

public section

namespace CFSG.RankThree.Co2

structure ClassFacts : Prop where
  mem : ∀ i < 10, repMat i ∈ Cm
  sq : ∀ i < 10, repMat i * repMat i = 1
  ne_one : ∀ i < 10, repMat i ≠ 1
  conj : ∀ i < 10, Nat.card {x : Matrix (Fin 22) (Fin 22) (ZMod 2) // CrConj (repMat i) x} =
    classSizes[i]!
  cent : ∀ i < 10, Nat.card {g : Matrix (Fin 22) (Fin 22) (ZMod 2) //
    g ∈ Cm ∧ g * repMat i = repMat i * g} * classSizes[i]! = 743178240

end CFSG.RankThree.Co2

end
