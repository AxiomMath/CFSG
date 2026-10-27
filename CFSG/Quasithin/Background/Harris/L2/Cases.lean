module

public import CFSG.Quasithin.Background.Harris.L2.Setup
public import CFSG.Quasithin.Background.Harris.Interfaces

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

@[expose] def Case6Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m n : ℕ), OneCompSetting Γ A L m → 2 ≤ n → ∀ φ : ↥L ≃* SL(2, GaloisField 2 n), m ≤ n →
    Nat.card (EndRing (repOf L φ)) = 2 ^ n → Module.finrank (EndRing (repOf L φ)) V = 2 →
    G93Case6 L m

@[expose] def Case7Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m a : ℕ), OneCompSetting Γ A L m → 1 ≤ a → ∀ φ : ↥L ≃* SL(2, GaloisField 2 (2 * a)),
    m ≤ 2 * a → Nat.card (EndRing (repOf L φ)) = 2 ^ a →
    Module.finrank (EndRing (repOf L φ)) V = 4 → G93Case7 L m

@[expose] def Case16Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m : ℕ), OneCompSetting Γ A L m → ∀ φ : ↥L ≃* SL(2, GaloisField 2 3), m ≤ 3 →
    Nat.card (EndRing (repOf L φ)) = 2 → Module.finrank (EndRing (repOf L φ)) V = 8 →
    G93Case16 L m

end CFSG.Quasithin.G11.Harris.L2
