module

public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEAssembly
public import CFSG.Quasithin.EmptyFaithfulMultiple.Assembly
public import CFSG.Quasithin.Background.SmithB57E
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.F918D9

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

theorem catalog_of_faithful_empty_of_inputs
    (h14 : UniqueCentralizerRecognitionStatement) (h56 : AsB56)
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
  catalog_of_faithful_empty h14 (multipleCentralizerRecognition_of_inputs h56 hGold) G hnonab hqtke
    T hMT hLf


theorem catalog_of_faithful_empty_of_b51_b42
    (h14 : UniqueCentralizerRecognitionStatement) (hB51 : AsB51) (hB42 : AsB42)
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
  catalog_of_faithful_empty_of_inputs h14 (FFC.asB56_of_exc_b59 B15P4.asB15Part4 hB51 hB42
      asA21SQTKSection (FFC.b57Exc_of B15P4.asB15Part4 hB51 asA21SQTKSection)
      (SmithB57.b59Last_holds hB51 hB42 asA21SQTKSection) asI16Cover_of) hGold G hnonab hqtke T hMT
    hLf

end CFSG.Quasithin.EmptyFaithfulMultiple
