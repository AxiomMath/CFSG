module

public import CFSG.LocalAnalysis.StandardType.GGResMaxRankDefs

public section

namespace CFSG.StandardType

theorem ggMaxRankPairing_chain (p : ℕ) (u v : ZMod p) (apos : Bool) (i j : Fin 8) :
    ggMaxRankPairing p u v apos (Sum.inl i) (Sum.inl j) = ((CartanMatrix.A 8 i j : ℤ) : ZMod p) := by
  fin_cases i <;> fin_cases j <;>
    simp [ggMaxRankPairing, ggMaxRankEdge, CartanMatrix.A]

theorem ggMaxRankPairing_chain_left (p : ℕ) (u v u' v' : ZMod p) (apos : Bool) (i : Fin 8)
    (o : Fin 8 ⊕ Fin 2) :
    ggMaxRankPairing p u v apos (Sum.inl i) o = ggMaxRankPairing p u' v' apos (Sum.inl i) o := by
  simp [ggMaxRankPairing]

theorem ggMaxRankPairing_chain_right (p : ℕ) (u v u' v' : ZMod p) (apos : Bool) (j : Fin 8)
    (o : Fin 8 ⊕ Fin 2) :
    ggMaxRankPairing p u v apos o (Sum.inl j) = ggMaxRankPairing p u' v' apos o (Sum.inl j) := by
  simp [ggMaxRankPairing]

theorem ggMaxRankPairing_cross (p : ℕ) (u v : ZMod p) (apos : Bool) :
    ggMaxRankPairing p u v apos (Sum.inr 1) (Sum.inr 0) = u ∧
      ggMaxRankPairing p u v apos (Sum.inr 0) (Sum.inr 1) = v := by
  constructor <;> simp [ggMaxRankPairing, ggMaxRankEdge]

theorem ggMaxRankPairing_extra_self (p : ℕ) (u v : ZMod p) (apos : Bool) (k : Fin 2) :
    ggMaxRankPairing p u v apos (Sum.inr k) (Sum.inr k) = 2 := by
  simp [ggMaxRankPairing]

theorem ggMaxRankPairing_extra_chain (p : ℕ) (u v : ZMod p) (j : Fin 8) :
    ggMaxRankPairing p u v false (Sum.inr 1) (Sum.inl j) =
      ggMaxRankPairing p 0 0 false (Sum.inr 0) (Sum.inl j) := by
  fin_cases j <;> simp [ggMaxRankPairing, ggMaxRankEdge]

theorem ggMaxRankPairing_chain_extra (p : ℕ) (u v : ZMod p) (j : Fin 8) :
    ggMaxRankPairing p u v false (Sum.inl j) (Sum.inr 1) =
      ggMaxRankPairing p 0 0 false (Sum.inl j) (Sum.inr 0) := by
  fin_cases j <;> simp [ggMaxRankPairing, ggMaxRankEdge]

end CFSG.StandardType

end
