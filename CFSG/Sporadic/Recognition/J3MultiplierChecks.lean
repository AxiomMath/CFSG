module

public import CFSG.Monster.Schur.CentralEps
public import CFSG.Sporadic.Recognition.J3MultiplierWords
public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.Sporadic.Recognition.J3Multiplier

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Recognition.CoverRecipe

@[expose] def flagsOf (n : ℕ) : Fin 2 → Bool := fun i => n.testBit i.val

@[expose] def flagNum (e : Fin 2 → Bool) : ℕ :=
  ((List.finRange 2).map fun i => if e i then 2 ^ i.val else 0).sum

@[expose] def epsWords (n : ℕ) : List (List (Fin (2 + 1) × Bool)) := epsRels U T (flagsOf n)

@[expose] def plainWords : List (List (Fin 2 × Bool)) := U ++ (List.finRange 2).map T

@[expose] def epsCheck (n : ℕ) : Bool :=
  subsetCheckShortCC (epsWords n) [1] 20 20000000 2643840

@[expose] def epsCheck₁ (n : ℕ) : Bool :=
  subsetCheckShortCC (restrictWords (subsetOf (2 + 1) [1]) (epsWords n)) [] 20 1000 19

@[expose] def plainCheck : Bool := subsetCheckShortCC plainWords [1] 20 20000000 2643840

@[expose] def plainCheck₁ : Bool :=
  subsetCheckShortCC (restrictWords (subsetOf 2 [1]) plainWords) [] 20 1000 19

theorem flagsOf_flagNum : ∀ e : Fin 2 → Bool, flagsOf (flagNum e) = e := by decide

theorem flagNum_pos_lt :
    ∀ e : Fin 2 → Bool, (∃ i, e i = true) → 1 ≤ flagNum e ∧ flagNum e < 4 := by
  decide

theorem bound_plain (h : plainCheck = true) (h₁ : plainCheck₁ = true) :
    Finite (PG 2 plainWords) ∧ Nat.card (PG 2 plainWords) ≤ 50232960 := by
  have := card_PG_le_chain_short h h₁
  exact ⟨this.1, this.2.trans (by norm_num)⟩

theorem bound_eps {n : ℕ} (h : epsCheck n = true) (h₁ : epsCheck₁ n = true) :
    Finite (PG (2 + 1) (epsWords n)) ∧ Nat.card (PG (2 + 1) (epsWords n)) ≤ 50232960 := by
  have := card_PG_le_chain_short h h₁
  exact ⟨this.1, this.2.trans (by norm_num)⟩

end CFSG.Sporadic.Recognition.J3Multiplier
