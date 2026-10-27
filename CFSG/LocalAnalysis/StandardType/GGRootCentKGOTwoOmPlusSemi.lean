module

public import CFSG.LieType.Universal.Spin.Chevalley.Plus

public section

namespace CFSG.StandardType.KGOm

open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {n : ℕ}

@[expose] def vPlusS (hn : 1 ≤ n) : Fin n ⊕ Fin n → K :=
  plusVec n K ⟨0, by omega⟩ true + plusVec n K ⟨0, by omega⟩ false

@[expose] noncomputable def plusSemi (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    (y : Fin n ⊕ Fin n → K) : Fin n ⊕ Fin n → K :=
  if ε then (fun m => τ (y m)) +
      QuadraticMap.polar (quadPlus n K) (vPlusS hn) (fun m => τ (y m)) • vPlusS hn
  else fun m => τ (y m)

theorem plusSemi_false (hn : 1 ≤ n) (τ : K ≃+* K) (y : Fin n ⊕ Fin n → K) :
    plusSemi hn false τ y = fun m => τ (y m) := rfl

theorem plusSemi_true (hn : 1 ≤ n) (τ : K ≃+* K) (y : Fin n ⊕ Fin n → K) :
    plusSemi hn true τ y = (fun m => τ (y m)) +
      QuadraticMap.polar (quadPlus n K) (vPlusS hn) (fun m => τ (y m)) • vPlusS hn := rfl

theorem plusSemi_false_one (hn : 1 ≤ n) (y : Fin n ⊕ Fin n → K) :
    plusSemi hn false 1 y = y := rfl

end CFSG.StandardType.KGOm
