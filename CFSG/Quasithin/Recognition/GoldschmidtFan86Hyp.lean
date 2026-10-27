module

public import CFSG.Quasithin.Recognition.GoldschmidtStatement
public import CFSG.Quasithin.Recognition.GoldschmidtGluing
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open CFSG.QuasithinUnique

structure Hyp53 {A C B : Type} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B) : Prop where
  finite_left : Finite A
  finite_right : Finite B
  faithful : X.IsFaithful
  pgroup : IsPGroup 2 C
  index_left : X.edgeA.index = 5
  index_right : X.edgeB.index = 3
  charTwo_left : CharTwo (⊤ : Subgroup A)
  charTwo_right : CharTwo (⊤ : Subgroup B)
  quot_left : Nonempty (oTwoQuot A ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot A ≃* ↥(Sz 0))
  quot_right : IsL2Quot 1 (oTwoQuot B)

@[expose] def FanMain : Prop :=
  (∀ (A C B : Type) [Group A] [Group C] [Group B] (X : GoldAmalgam A C B), Hyp53 X →
      ¬ Nonempty (oTwoQuot A ≃* DihedralGroup 5) ∧ (Nat.card C = 2 ^ 11 ∨ Nat.card C = 2 ^ 12)) ∧
  ∀ (A C B A' C' B' : Type) [Group A] [Group C] [Group B] [Group A'] [Group C'] [Group B']
    (X : GoldAmalgam A C B) (X' : GoldAmalgam A' C' B'), Hyp53 X → Hyp53 X' →
      Nat.card C = Nat.card C' → X.IsIso X'

@[expose] def ModelFacts : Prop :=
  (∃ (Y : Type) (_ : Group Y) (T M₁ M₂ : Subgroup Y), Nonempty (Y ≃* quasithinTits) ∧
      IsYAmalgamPair T M₁ M₂ ∧ Hyp53 (GoldAmalgam.ofSubgroupPair M₁ M₂) ∧
      Nat.card ↥(M₁ ⊓ M₂) = 2 ^ 11 ∧ Nat.card ↥(pCoreOf 2 M₁) = 2 ^ 9 ∧
      Nat.card ↥(pCoreOf 2 M₂) = 2 ^ 10) ∧
  (∃ (Y : Type) (_ : Group Y) (T M₁ M₂ : Subgroup Y), IsTwistedF4Over 1 Y ∧
      IsYAmalgamPair T M₁ M₂ ∧ Hyp53 (GoldAmalgam.ofSubgroupPair M₁ M₂) ∧
      Nat.card ↥(M₁ ⊓ M₂) = 2 ^ 12 ∧ Nat.card ↥(pCoreOf 2 M₁) = 2 ^ 10 ∧
      Nat.card ↥(pCoreOf 2 M₂) = 2 ^ 11)

end CFSG.Quasithin.Fan86
