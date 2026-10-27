module

public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.Quasithin.Recognition.St84.Gen.BigL2Slice

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IdL2L2GenW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (m n : ℕ),
    F112HypW L1 L2 S → 2 ≤ m → 2 ≤ n → ¬ (m = 2 ∧ n = 2) →
      IsL2Quot m (oTwoQuot ↥L1) → IsL2Quot n (oTwoQuot ↥L2) →
        (m = n ∧ (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 n) ∨
            IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over n) ∨
            IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over n))) ∨
          (m = 3 * n ∧ IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 n)) ∨
          (n = 3 * m ∧ IsAmalgamOfGroup (f112Amalgam L2 L1 S) (IsLieOverTwo .trialityD4 0 m)) ∨
          (n = 2 * m ∧ (IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 m) ∨
            IsU4ExtTwo m (f112Amalgam L1 L2 S))) ∨
          (m = 2 * n ∧ (IsAmalgamOfGroup (f112Amalgam L2 L1 S) (IsLieOverTwo .PSU 4 n) ∨
            IsU4ExtTwo n (f112Amalgam L2 L1 S)))

theorem IdL2L2GenW.idL2L2Gen (h : IdL2L2GenW) : IdL2L2Gen :=
  fun G _ _ L1 L2 S m n hF => h G L1 L2 S m n hF.toW

@[expose] def IdA5A5W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112HypW L1 L2 S → VA5 L1 → VA5 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 2) ∨
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over 2) ∨
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2)

theorem IdA5A5W.idA5A5 (h : IdA5A5W) : IdA5A5 :=
  fun G _ _ L1 L2 S hF => h G L1 L2 S hF.toW

end CFSG.Quasithin.F112R

end
