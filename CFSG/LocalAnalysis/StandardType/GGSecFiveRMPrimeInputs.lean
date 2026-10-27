module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveRootGenLInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ r ∈ ggAutomizer L Bs, GGIsReflection p r → GGRealized p Bs r

@[expose] def GGSecFiveLevTwoInput' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G), p.Prime → p ≠ 2 →
    IsElemAbelian p Bs → GGNoTransvection p Bs →
      ∀ (A : Subgroup (MulAut ↥Bs)), A ≤ ggInduced ⊤ Bs →
        ∀ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M →
          (¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e) →
          ∀ f : M.Group ≃* ↥A, (∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)) →
          ∀ (x : ↥Bs) (AL : Subgroup (MulAut ↥Bs)) (ιL : Type) [Fintype ιL]
            (ML : CoxeterMatrix ιL), AL ≤ A → (∀ a ∈ AL, a x = x) →
            (GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) → GGWeylOfType p ML AL →
            Nat.card ↥Bs ≤ p ^ (Fintype.card ιL + 1) →
            (∀ a ∈ A, GGIsReflection p a → a x = x →
              (∃ g ∈ A, ∃ r ∈ AL, GGIsReflection p r ∧ a = g * r * g⁻¹) → a ∈ AL) →
            ∀ 𝒮 : Set (Subgroup (MulAut ↥Bs)),
              (∀ K ∈ 𝒮, K ≤ A ∧ K = Subgroup.closure {a | a ∈ K ∧ GGIsReflection p a}) →
              ∃ 𝒮' : Finset (Subgroup (MulAut ↥Bs)), (𝒮' : Set (Subgroup (MulAut ↥Bs))) ⊆ 𝒮 ∧
                𝒮'.card ≤ 2 ∧ AL ⊔ ⨆ K ∈ 𝒮, K = AL ⊔ ⨆ K ∈ 𝒮', K

end CFSG.StandardType
