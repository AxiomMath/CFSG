module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres2
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtGluing

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

variable {A C B : Type*} [Group A] [Group C] [Group B]

@[expose] def AmalgamLink (X : GoldAmalgam A C B) (a : A) (b : B) : Prop :=
  ∃ c : C, X.toA c = a ∧ X.toB c = b

structure PresLinks (X : GoldAmalgam A C B) (w za : A) (y z : Fin 5 → A) (t w1 w2 ub : B)
    (zm ym za' : Fin 3 → B) : Prop where
  lt : AmalgamLink X (y 0) t
  lw1 : AmalgamLink X w w1
  lw2 : AmalgamLink X (y 3 * y 4 * z 3) w2
  lub : AmalgamLink X (z 0 * z 4 * (z 2 * za)) ub
  lzm0 : AmalgamLink X (z 0) (zm 0)
  lzm1 : AmalgamLink X (y 0 * (w ^ 2 * za) * y 0) (zm 1)
  lzm2 : AmalgamLink X (w ^ 2 * za) (zm 2)
  lym0 : AmalgamLink X (z 0 * z 1) (ym 0)
  lym1 : AmalgamLink X (z 0 * z 1 * (y 2 * z 2)) (ym 1)
  lym2 : AmalgamLink X (y 2 * z 2) (ym 2)
  lza0 : AmalgamLink X za (za' 0)
  lza1 : AmalgamLink X (z 2 * za) (za' 1)
  lza2 : AmalgamLink X (z 2) (za' 2)

@[expose] def AdmitsPres11 (X : GoldAmalgam A C B) : Prop :=
  ∃ (x w za : A) (y z : Fin 5 → A) (xb t w1 w2 ub : B) (zm ym za' : Fin 3 → B),
    P1Rel x w za y z ∧ P2Rel912 xb t w1 w2 ub zm ym za' ∧
      P2Rel913 0 0 xb t w1 w2 ub zm ym za' ∧
      Subgroup.closure (({x, w, za} : Set A) ∪ Set.range y ∪ Set.range z) = ⊤ ∧
      Subgroup.closure (({xb, t, w1, w2, ub} : Set B) ∪ Set.range zm ∪ Set.range ym ∪
        Set.range za') = ⊤ ∧
      Subgroup.closure (({t, w1, w2, ub} : Set B) ∪ Set.range zm ∪ Set.range ym ∪
        Set.range za') = X.edgeB ∧
      PresLinks X w za y z t w1 w2 ub zm ym za'

@[expose] def AdmitsPres12 (X : GoldAmalgam A C B) : Prop :=
  ∃ (x w za c : A) (y z : Fin 5 → A) (xb t w1 w2 ub cb : B) (zm ym za' : Fin 3 → B),
    P1Rel x w za y z ∧ P1cRel x za c y z ∧ fcomm w c = 1 ∧
      P2Rel912 xb t w1 w2 ub zm ym za' ∧ P2cRel912 ub cb zm ym za' ∧
      P2Rel913 0 0 xb t w1 w2 ub zm ym za' ∧ P2cRel913 0 xb t w1 w2 cb zm ym za' ∧
      Subgroup.closure (({x, w, za, c} : Set A) ∪ Set.range y ∪ Set.range z) = ⊤ ∧
      Subgroup.closure (({xb, t, w1, w2, ub, cb} : Set B) ∪ Set.range zm ∪ Set.range ym ∪
        Set.range za') = ⊤ ∧
      Subgroup.closure (({t, w1, w2, ub, cb} : Set B) ∪ Set.range zm ∪ Set.range ym ∪
        Set.range za') = X.edgeB ∧
      PresLinks X w za y z t w1 w2 ub zm ym za' ∧ AmalgamLink X c cb

@[expose] def AdmitsPres (n : ℕ) (X : GoldAmalgam A C B) : Prop :=
  (n = 11 ∧ AdmitsPres11 X) ∨ (n = 12 ∧ AdmitsPres12 X)

@[expose] def IsoOfAdmitsPres : Prop :=
  ∀ (n : ℕ) (A C B A' C' B' : Type) [Group A] [Group C] [Group B] [Group A'] [Group C']
    [Group B'] (X : GoldAmalgam A C B) (X' : GoldAmalgam A' C' B'),
    X.edgeA.index = 5 → X.edgeB.index = 3 → X'.edgeA.index = 5 → X'.edgeB.index = 3 →
    Nat.card C = 2 ^ n → Nat.card C' = 2 ^ n → AdmitsPres n X → AdmitsPres n X' → X.IsIso X'

end CFSG.Quasithin.Fan86
