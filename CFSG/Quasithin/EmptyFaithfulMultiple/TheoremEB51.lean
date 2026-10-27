module

public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB42
public import CFSG.Quasithin.Background.SmithB51SL3Main

public section

namespace CFSG.Quasithin

namespace B5

theorem asB51NonirrSL3IH_holds :
    AsB51NonirrSL3IH :=
  asB51NonirrSL3Ind_holds asB42_holds asA21SQTKSection asA36NoOddCover_holds

theorem asB51_holds :
    AsB51 :=
  asB51_of_nonirrSL3IH asB51NonirrSL3IH_holds

end B5

theorem asB56_holds :
    AsB56 :=
  asB56_of_b51 B5.asB51_holds

end CFSG.Quasithin

namespace CFSG.Quasithin.EmptyFaithfulMultiple

theorem catalog_of_faithful_empty_of_unique_gold
    (h14 : UniqueCentralizerRecognitionStatement) (hGold : F6.GoldschmidtCharTwoLarge.{0})
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G,
      ¬ CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Blueprint.Catalog G :=
  catalog_of_faithful_empty_of_b51 h14 B5.asB51_holds hGold G hnonab hqtke T hMT hLf

end CFSG.Quasithin.EmptyFaithfulMultiple
