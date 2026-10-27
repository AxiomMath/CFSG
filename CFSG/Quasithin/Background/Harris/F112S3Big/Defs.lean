module

public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.Background.Harris.F112S3Big

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

@[expose] def F112B6Loc (L1 L2 : Subgroup G) : Prop :=
  IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 L1) ∧
    IsBlock2 L2 L2 ∧ IsL2Quot 2 (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 1 ∧ IsAltType L2 5

@[expose] def F112B4Loc (L1 L2 : Subgroup G) : Prop :=
  IsL2Quot 3 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 4 ↥(pCoreOf 2 L1) ∧
    IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 11

@[expose] def F112B10Loc (L1 L2 : Subgroup G) : Prop :=
  IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 L1) ∧
    IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6

@[expose] def F112B11Loc (L1 L2 S : Subgroup G) : Prop :=
  Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 L1) ∧
    Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6

@[expose] def F112ListBLoc (L1 L2 S : Subgroup G) : Prop :=
  F112B4Loc L1 L2 ∨ F112B6Loc L1 L2 ∨ F112B10Loc L1 L2 ∨ F112B11Loc L1 L2 S

end CFSG.Quasithin.Background.Harris.F112S3Big
