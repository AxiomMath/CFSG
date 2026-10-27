module

public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Background.E2TwoLieQuot
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Stmt5_2_3S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H V : Subgroup G) (m : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    2 ≤ m → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 m →
    IsHStar T M H → (∃ K ∈ cComp H, E2.HasE22LieQuot K) →
    V ≤ L ⊔ T → IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) → ⁅V, L⁆ ≠ ⊥ →
      (m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆ ∧ CentralizerComponentClause T H) ∨
      Nonempty (G ≃* NativeSporadic.M23) ∨ Alt12_2_2Lie G

end CFSG.Quasithin.H13
