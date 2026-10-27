module

public import Certificates.Kernel.NFMK.Glue

public section

public section

namespace Certificates

open CFSG.StandardType.ZS in
theorem certificate709544 :
    (∃ t : Fin 4 → ↥(model .N4),
      (∀ i, ((t i).1 : Matrix (Fin (mdeg .N4)) (Fin (mdeg .N4)) (ZMod 13)) =
        ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat] i) ∧
      Subgroup.closure (Set.range t) = ⊤ ∧ 7680 ≤ Nat.card (model .N4) ∧
      (∀ N : Subgroup ↥(model .N4), N.Normal → N ≠ ⊥ → (n4ZW.map t).prod ∈ N) ∧
      Nat.card (Subgroup.center ↥(model .N4)) = 4 ∧
      (∀ g h : ↥(model .N4), _root_.IsConj (t 0) g → _root_.IsConj (t 0) h → orderOf (g * h) ≤ 4) ∧
      (∀ g : ↥(model .N4), g * g = 1 → g = 1 ∨ _root_.IsConj (t 0) g ∨
        _root_.IsConj (t 0) ((n4ZW.map t).prod * g) ∨
        (∃ a b, _root_.IsConj (t 0) a ∧ _root_.IsConj (t 0) b ∧ g = a * b) ∨
        ∃ a b, _root_.IsConj (t 0) a ∧ _root_.IsConj (t 0) b ∧ g = (n4ZW.map t).prod * (a * b)) ∧
      IsReflMat (t 0).1 ∧ orderOf (t 0 * t 2) = 4) ∧
    (∃ t : Fin 5 → ↥(model .EN4),
      (∀ i, ((t i).1 : Matrix (Fin (mdeg .EN4)) (Fin (mdeg .EN4)) (ZMod 13)) =
        ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat,
          Matrix.diagonal fun j => if j = 3 then -1 else 1] i) ∧
      Subgroup.closure (Set.range t) = ⊤ ∧ 46080 ≤ Nat.card (model .EN4) ∧
      (∀ N : Subgroup ↥(model .EN4), N.Normal → N ≠ ⊥ → (en4ZW.map t).prod ∈ N) ∧
      Nat.card (Subgroup.center ↥(model .EN4)) = 4 ∧
      (∀ g h : ↥(model .EN4), _root_.IsConj (t 0) g → _root_.IsConj (t 0) h → orderOf (g * h) ≤ 4) ∧
      (∀ g : ↥(model .EN4), g * g = 1 → g = 1 ∨ _root_.IsConj (t 0) g ∨
        _root_.IsConj (t 0) ((en4ZW.map t).prod * g) ∨
        (∃ a b, _root_.IsConj (t 0) a ∧ _root_.IsConj (t 0) b ∧ g = a * b) ∨
        ∃ a b, _root_.IsConj (t 0) a ∧ _root_.IsConj (t 0) b ∧ g = (en4ZW.map t).prod * (a * b)) ∧
      IsReflMat (t 0).1 ∧ orderOf (t 0 * t 2) = 4) :=
  ⟨CFSG.StandardType.ZS.NFMK.nfmk_n4, CFSG.StandardType.ZS.NFMK.nfmk_en4⟩

end Certificates

end

end
