module

public import Certificates.Data.Kernel.Misc.Coset.Act
public import Certificates.Data.Kernel.Misc.RuInv
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverNative
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.KC.Misc.RuCover

open CFSG.KC.Enum CFSG.KC.MiscCoset.Act CFSG.KC.Misc.RuInv CFSG.Quasithin.KGC31.RuCover

@[expose] noncomputable def selL {α : Sort _} (q₀ q₁ q₂ q₃ : α) (l : Int) : α :=
  Int.rec (motive := fun _ => α) (fun n => Bool.rec q₂ q₀ (Nat.beq n 1))
    (fun n => Bool.rec q₃ q₁ (Nat.beq n 0)) l

@[expose] noncomputable def walkW (A : Nat → Nat) (Q₀ Q₁ Q₂ Q₃ : List Nat) (w : List Int)
    (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun l _ ih y => strictN (walk A (nat_lit 6) (selL Q₀ Q₁ Q₂ Q₃ l) y) ih) w x

@[expose] noncomputable def walkP (P₀ P₁ P₂ P₃ : Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun l _ ih y => strictN (apP (selL P₀ P₁ P₂ P₃ l) y) ih) w x

@[expose] noncomputable def eqOK (A : Nat → Nat) (Q₀ Q₁ Q₂ Q₃ : List Nat) (P₀ P₁ P₂ P₃ : Nat)
    (x y : List Int) : Bool :=
  CFSG.KC.MiscCoset.Act.andB (Nat.beq (walkW A Q₀ Q₁ Q₂ Q₃ x (nat_lit 0)) (walkW A Q₀ Q₁ Q₂ Q₃ y (nat_lit 0)))
    (allR (nat_lit 0) (nat_lit 4) fun b =>
      Nat.beq (walkP P₀ P₁ P₂ P₃ x b) (walkP P₀ P₁ P₂ P₃ y b))

@[expose] noncomputable def etaW (c : Nat) (m : Nat) : List Int :=
  Nat.rec (motive := fun _ => List Int) []
    (fun j ih => ih ++ cond (c.testBit j) (eW.getD j []) []) m

@[expose] noncomputable def tabCode (j i : Nat) : Nat := (tabC.getD j []).getD i 0

@[expose] noncomputable def eqPair (k : Nat) : List Int × List Int :=
  [(eW.getD 0 [] ++ eW.getD 0 [], []), (eW.getD 1 [] ++ eW.getD 1 [], []),
    (eW.getD 2 [] ++ eW.getD 2 [], []),
    (eW.getD 0 [] ++ eW.getD 1 [], eW.getD 1 [] ++ eW.getD 0 []),
    (eW.getD 0 [] ++ eW.getD 2 [], eW.getD 2 [] ++ eW.getD 0 []),
    (eW.getD 1 [] ++ eW.getD 2 [], eW.getD 2 [] ++ eW.getD 1 []),
    (nW.getD 0 [] ++ eW.getD 0 [], etaW (tabCode 0 0) 3 ++ nW.getD 0 []),
    (nW.getD 0 [] ++ eW.getD 1 [], etaW (tabCode 0 1) 3 ++ nW.getD 0 []),
    (nW.getD 0 [] ++ eW.getD 2 [], etaW (tabCode 0 2) 3 ++ nW.getD 0 []),
    (nW.getD 1 [] ++ eW.getD 0 [], etaW (tabCode 1 0) 3 ++ nW.getD 1 []),
    (nW.getD 1 [] ++ eW.getD 1 [], etaW (tabCode 1 1) 3 ++ nW.getD 1 []),
    (nW.getD 1 [] ++ eW.getD 2 [], etaW (tabCode 1 2) 3 ++ nW.getD 1 [])].getD k ([], [])

end CFSG.KC.Misc.RuCover

end
