module

public import CFSG.Quasithin.Recognition.F112J2Split

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def vBeta (K1 L2 S Zs : Subgroup G) : Subgroup G :=
  conjClosure (conjClosure Zs L2) (K1 ⊔ S)

end Defs

@[expose] def F112R1aAbelianStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    IsL2Quot 2 (OTwoQuot K1) → ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = ⊥ → False

end CFSG.Quasithin
