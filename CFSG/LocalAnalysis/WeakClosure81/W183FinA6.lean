module

public import CFSG.LocalAnalysis.WeakClosure81.W183Fin2
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.LocalAnalysis.WeakClosure81.W183FinA6Aux2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

theorem finA6_holds : FinA6 :=
  w183fin_finA6

theorem finG3A6_holds : ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal →
    Subgroup.centralizer (L : Set Y) = ⊥ → IsAlt ↥L 6 →
    ∀ A : Subgroup Y, Nat.card A = 4 → CFSG.Open.IsElemAbelian 2 A →
      (∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) → False :=
  w183fin_finG3_A6

theorem finGraphOddA6_holds :
    ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsAlt ↥L 6 →
      Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
      ∀ a : Y, orderOf a = 2 →
        ¬ CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : Y | IsConj a x} :=
  w183fin_finGraphOdd_A6

end CFSG.LocalAnalysis.WeakClosure81

end
