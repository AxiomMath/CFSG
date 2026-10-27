module

public import CFSG.Quasithin.MS93.SkItems
public import CFSG.Quasithin.MS93.ML3Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def MS18Int : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L U V : Subgroup G} {F : Type} [Field F] [Fintype F] {n : ℕ},
    Fintype.card F = 2 ^ n → ∀ {α : ↥L →* ↥(StatedSL 3 F)}, Function.Surjective α →
    (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) → (∀ v ∈ V, v ^ 2 = 1) →
    (∀ l : ↥L, α l = 1 → ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ = v) → SQTKGroup (SL3 F) →
    IsSumOfNaturalModulesVia L U ⊥ α false 1 → IsSumOfNaturalModulesVia L V U α false 1 →
    IsSumOfNaturalModulesVia L V ⊥ α false 2

@[expose] def S36Sp4Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    critDist (puAmalgam h.le) = 2 → Vq M L ≠ Uq M T L →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
      ¬ ⁅ZM (puAmalgam h.le) α', Qv (puAmalgam h.le) (baseA _)⁆ ≤
          ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
            ⁅critA (puAmalgam h.le) (baseA _) α', Qv (puAmalgam h.le) (baseA _)⁆ →
      S33iiW h α' → False

end CFSG.Quasithin.MS93
