module

public import CFSG.Quasithin.EmptyFaithful.TopAssemblyFrontier23
public import CFSG.Quasithin.MS93.C134L32CorrMHolds
public import CFSG.Quasithin.MS93.MResSq
public import CFSG.Quasithin.EmptyFaithful.TopAssemblyFrontier21
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEUnique

public section

namespace CFSG.Quasithin

theorem qtfe_six_models_frontier24
    (hSp : MS93.MRes.S34FDescSp4) :
    ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G),
      quasithinQTFE14Cat G T Mc → NativeSixModels G :=
  qtfe_six_models_of_c13s (MS93.MRes.asC132_of_descSp4 (MS93.MRes.descSp4_of_fDescSp4 hSp))
    MS93.c134L32CorrM_holds MS93.MRes.asC134_corrWOneSq_holds

theorem qtfe_unique_centralizer_of_two
    (hSp4 : MS93.S4L.NoNonlinSp4) (hSpGt4 : MS93.S4L.NoNonlinSpGt4) :
    ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G),
      quasithinQTFE14Cat G T Mc → NativeSixModels G :=
  qtfe_six_models_frontier24 (MS93.MRes.s34FDescSp4_of_noNonlin hSp4 hSpGt4)

theorem qt_faithful_local_empty_of_two
    (hSp4 : MS93.S4L.NoNonlinSp4) (hSpGt4 : MS93.S4L.NoNonlinSpGt4) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
      ∀ (T : Sylow 2 G),
        (∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
          Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
          Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
          (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂) →
        (∀ L : Subgroup G, ¬ Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) →
        Blueprint.Catalog G := by
  intro G _ _ _ hnonab hqtke T hMT hLf
  have hUC : EmptyFaithfulMultiple.UniqueCentralizerRecognitionStatement :=
    fun G _ _ T Mc h => qtfe_unique_centralizer_of_two hSp4 hSpGt4 G T Mc h
  exact EmptyFaithfulMultiple.catalog_of_faithful_empty_of_unique_centralizer hUC G hnonab hqtke
    T hMT hLf

end CFSG.Quasithin
