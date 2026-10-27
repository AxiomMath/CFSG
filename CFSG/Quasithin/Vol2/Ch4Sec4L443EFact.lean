module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.Quasithin

@[expose] def A382List (X : Type) [Group X] : Prop :=
  (∃ n, IsPSL 2 2 n X) ∨ (∃ n, IsSz n X) ∨ IsSporadic .J1 X ∨
    (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e X) ∨ IsSU3 8 X

@[expose] def Fact4411 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → A382List K →
    ∀ U Y : Subgroup (K ⧸ Subgroup.center K), IsPGroup 2 U → ⁅Y, Y⁆ = Y →
      Y ≤ Subgroup.normalizer (U : Set (K ⧸ Subgroup.center K)) → ⁅U, Y⁆ = ⊥

end CFSG.Quasithin.H13.Ch4.E443
