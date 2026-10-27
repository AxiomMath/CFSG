module

public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.SmithB51Assembly
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEInputs

public section

namespace CFSG.Quasithin

namespace B5

theorem asB51_of_nonirrSL3IH
    (hSL3 : AsB51NonirrSL3IH) : AsB51 :=
  asB51_of_open asB42_holds hSL3

end B5

theorem asB56_of_b51
    (hB51 : AsB51) : AsB56 :=
  FFC.asB56_of_exc_b59 B15P4.asB15Part4 hB51 asB42_holds asA21SQTKSection
      (FFC.b57Exc_of B15P4.asB15Part4 hB51 asA21SQTKSection)
      (SmithB57.b59Last_holds hB51 asB42_holds asA21SQTKSection) asI16Cover_of

end CFSG.Quasithin

namespace CFSG.Quasithin.EmptyFaithfulMultiple

theorem catalog_of_faithful_empty_of_b51
    (h14 : UniqueCentralizerRecognitionStatement) (hB51 : AsB51)
    (hGold : F6.GoldschmidtCharTwoLarge.{0})
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G,
      ¬ CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Blueprint.Catalog G :=
  catalog_of_faithful_empty_of_b51_b42 h14 hB51 asB42_holds hGold G hnonab hqtke T hMT hLf

end CFSG.Quasithin.EmptyFaithfulMultiple
