module

public import CFSG.Quasithin.Recognition.Stroth.SliceSplit
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F112R

@[expose] def IdSzL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112Hyp L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsTwistedF4Over (2 * a + 1))

@[expose] def IdU3L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VU3Big L1 → VBig L2 → VL2 L2 →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
          Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 4 F)) ∧
        IsL2Quot 4 (oTwoQuot ↥L2) ∧
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 5 2)

@[expose] def Y9TwistedF4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112Hyp L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsTwistedF4Over (2 * a + 1)) →
        centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∧
          Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 ∧
          Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11 ∧
          PerfectOver L1 L2 S

@[expose] def Y9U54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
          Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 4 F)) →
      IsL2Quot 4 (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 5 2) →
        centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∧
          IsSpecialPow 2 4 3 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 16 ∧
          PerfectOver L1 L2 S

open CFSG.Quasithin.H13

end CFSG.Quasithin.Stroth
