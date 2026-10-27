module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

abbrev L32WrZ2 : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2)

@[expose] def GoodShape152 {G : Type} [Group G] (X : Subgroup G) : Prop :=
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsAutLnTwo n (OTwoQuot X)) ∨ Nonempty (OTwoQuot X ≃* L32WrZ2)

@[expose] def Insp15227ParGood : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    ¬ V154 T Mc M ≤ pCoreOf 2 Mc →
    (Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212iii T Mc (conjClosure (oTwoUpper H) Mc)) →
    GoodShape152 (conjClosure (oTwoUpper H) Mc ⊔ T) →
    ∀ P : Subgroup G, P ∈ uFamHat (conjClosure (oTwoUpper H) Mc ⊔ T) T → ¬ P ≤ M → IsHStar T M P

@[expose] def Insp15227Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    ¬ V154 T Mc M ≤ pCoreOf 2 Mc →
    (Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
      Case15212iii T Mc (conjClosure (oTwoUpper H) Mc)) →
    ∀ L N : Subgroup G, IsChiefStep (conjClosure (oTwoUpper H) Mc ⊔ T) (pCoreOf 2 Mc) L N →
      quasithinOmegaOneCenter T ≤ L → ¬ ⁅N, V154 T Mc M⁆ ≤ L →
      Nat.card ↥(⁅N, V154 T Mc M⁆ ⊔ L) ≤ 4 * Nat.card ↥L →
      GoodShape152 (conjClosure (oTwoUpper H) Mc ⊔ T)

end CFSG.Quasithin
