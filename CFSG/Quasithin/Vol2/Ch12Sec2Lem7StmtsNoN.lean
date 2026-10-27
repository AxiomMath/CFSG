module

public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem1227ListEqNoN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T K VY H M₀ : Subgroup G), Hyp1223 G T K VY →
    T ≤ Subgroup.normalizer (VY : Set G) → (∃ _ : IsMulCommutative ↥VY, Modules12_2_2 K VY) →
    H = K ⊔ T → MinParabolic H T M₀ → E2.E22CasesNoN H T M₀ K →
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 2 2

@[expose] def Lem1227ListLtNoN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T K Y VY H M₀ : Subgroup G), Hyp1223 G T Y VY →
    T ≤ Subgroup.normalizer (VY : Set G) → (∃ _ : IsMulCommutative ↥VY, Modules12_2_2 Y VY) →
    quasithinIsLocal T K → K < Y → T ≤ Subgroup.normalizer (K : Set G) →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → H = K ⊔ T → MinParabolic H T M₀ →
    E2.E22CasesNoN H T M₀ K →
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 2 2 ∧
        Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
          alternatingGroup (Fin 7))

end CFSG.Quasithin.H13
