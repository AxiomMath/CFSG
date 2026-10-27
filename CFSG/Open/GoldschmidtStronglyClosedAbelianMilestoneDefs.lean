module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.Fitting.WholeGroupConstruction

public section

namespace CFSG.Open

open CFSG.Open

open Matrix
open scoped MatrixGroups

@[expose] def goldschmidtOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance goldschmidtOddCore_normal (H : Type*) [Group H] : (goldschmidtOddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def goldschmidtLayer (Q : Type*) [Group Q] : Subgroup Q :=
  CFSG.WholeGroup.layerOf fun K : Subgroup Q => IsComponentOf K ⊤

theorem goldschmidtLayer.eq_sSup (Q : Type*) [Group Q] :
    goldschmidtLayer Q = sSup {K : Subgroup Q | IsComponentOf K ⊤} :=
  rfl

attribute [eqns goldschmidtLayer.eq_sSup] goldschmidtLayer

@[expose] def goldschmidtJ1GenA : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 7, 9, 9, 10, 7, 9;
     7, 0, 1, 4, 3, 3, 4;
     9, 1, 2, 8, 3, 6, 2;
     9, 4, 8, 10, 1, 6, 0;
     10, 3, 3, 1, 8, 9, 1;
     7, 3, 6, 6, 9, 1, 3;
     9, 4, 2, 0, 1, 3, 0]

@[expose] def goldschmidtJ1GenB : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![5, 7, 1, 8, 5, 8, 2;
     10, 4, 10, 0, 3, 3, 8;
     5, 10, 8, 9, 1, 2, 1;
     2, 3, 3, 6, 1, 2, 9;
     7, 4, 7, 2, 10, 7, 3;
     3, 9, 0, 4, 2, 3, 5;
     3, 4, 3, 3, 9, 4, 9]

@[expose] def goldschmidtJ1 : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {g | (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = goldschmidtJ1GenA ∨
    (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = goldschmidtJ1GenB}

@[expose] def goldschmidtSimpleType (L : Type) [Group L] : Prop :=
  (∃ f : ℕ, 3 ≤ f ∧ Nonempty (L ≃* PSL(2, GaloisField 2 f))) ∨
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (L ≃* Sz n)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ Nonempty (L ≃* PSU3 2 f)) ∨
  (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f))) ∨
  (∃ m : ℕ, 1 ≤ m ∧ Nat.card L = ordRee (3 ^ (2 * m + 1))) ∨
  Nonempty (L ≃* goldschmidtJ1)

end CFSG.Open
