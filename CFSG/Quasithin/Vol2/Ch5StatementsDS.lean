module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Lists

variable {G : Type} [Group G]

@[expose] def F112ListALegacyBare (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 f) ∧
      IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsSp4Over f) ∧
      IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsG2Over f) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ S)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ S)) = (2 ^ f) ^ 5) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 f) ∧
      IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 L1) ∧
      IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = (2 ^ f) ^ 11) ∨
  (∃ a : ℕ, 1 ≤ a ∧ IsAmalgamOfGroup α (IsTwistedF4Over (2 * a + 1)) ∧
      Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∧ Nat.card (pCoreOf 2 L1) = (2 ^ (2 * a + 1)) ^ 10 ∧
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = (2 ^ (2 * a + 1)) ^ 11) ∨
  (∃ f : ℕ, 2 ≤ f ∧ (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 f) ∨ IsU4ExtTwo f α) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L1) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 f) ∨
  (IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 L1) ∧ IsL2Quot 4 (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 L2) = 2 ^ 16)

@[expose] def F112ListBLegacyBare (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 1) ∧
      IsL2Quot 3 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 4 ↥(pCoreOf 2 L1) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 11) ∨
  ((IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 1) ∨ IsU4ExtTwo 1 α) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 L1) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot 2 (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 1 ∧
      IsAltType L2 5) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 L1) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 L1) ∧
      Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 L2) = 2 ^ 6)

@[expose] def F112ListA (L1 L2 S : Subgroup G) : Prop :=
  let P1 := L1 ⊔ bigB L1 L2 S
  let P2 := L2 ⊔ bigB L1 L2 S
  let α := RankTwoAmalgam.ofSubgroups P1 P2
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 f) ∧
      IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsSp4Over f) ∧
      IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsG2Over f) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 P1) ∧
      Nat.card (pCoreOf 2 P2) = (2 ^ f) ^ 5) ∨
  (∃ f : ℕ, 2 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 f) ∧
      IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 P1) ∧
      IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 P2) = (2 ^ f) ^ 11) ∨
  (∃ a : ℕ, 1 ≤ a ∧ IsAmalgamOfGroup α (IsTwistedF4Over (2 * a + 1)) ∧
      Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∧ Nat.card (pCoreOf 2 P1) = (2 ^ (2 * a + 1)) ^ 10 ∧
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 P2) = (2 ^ (2 * a + 1)) ^ 11) ∨
  (∃ f : ℕ, 2 ≤ f ∧ (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 f) ∨ IsU4ExtTwo f α) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 P1) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 f) ∨
  (IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 P1) ∧ IsL2Quot 4 (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 P2) = 2 ^ 16)

@[expose] def F112ListB (L1 L2 S : Subgroup G) : Prop :=
  let P1 := L1 ⊔ bigB L1 L2 S
  let P2 := L2 ⊔ bigB L1 L2 S
  let α := RankTwoAmalgam.ofSubgroups P1 P2
  (IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 1) ∧
      IsL2Quot 3 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 4 ↥(pCoreOf 2 P1) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 P2) = 2 ^ 11) ∨
  ((IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 1) ∨ IsU4ExtTwo 1 α) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsSpecialPow 2 2 2 ↥(pCoreOf 2 P1) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot 2 (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 1 ∧
      IsAltType L2 5) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 P1) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 P2) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧ IsQ8D8 ↥(pCoreOf 2 P1) ∧
      Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pCoreOf 2 P2) = 2 ^ 6)

end Lists

end CFSG.Quasithin.H13
