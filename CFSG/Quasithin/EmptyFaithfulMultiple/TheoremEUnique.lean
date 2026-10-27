module

public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

theorem catalog_of_faithful_empty_of_unique_centralizer
    (h14 : UniqueCentralizerRecognitionStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G,
      ¬ CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Blueprint.Catalog G :=
  catalog_of_faithful_empty_of_unique_gold h14 F6.GoldAmLarge.goldschmidtCharTwoLarge_holds G
    hnonab hqtke T hMT hLf

end CFSG.Quasithin.EmptyFaithfulMultiple
