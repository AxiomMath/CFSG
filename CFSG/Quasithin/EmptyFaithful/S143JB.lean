module

public import CFSG.Quasithin.EmptyFaithful.S143JA
public import CFSG.Quasithin.EmptyFaithful.S143HA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

@[expose] def Lemma14319SixRestSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl19a T M → IsA6Block (kOf T M A) A →
      (∃ X : Subgroup (DihedralGroup 4), Nonempty (↥(dOf T M) ≃* ↥X)) ∧
        (Nonempty (↥(dOf T M) ≃* DihedralGroup 4) ↔
          ((kOf T M A).relIndex (Subgroup.normalizer (kOf T M A : Set G)) = 4 ∧
            A < Subgroup.centralizer (A : Set G))) ∧
        Subgroup.normalizer (A : Set G) = Subgroup.normalizer (kOf T M A : Set G)

theorem lemma14319TenFiveSixSeven_of_rest (h : Lemma14319SixRestSeven) :
    Lemma14319TenFiveSixSeven := by
  intro G _ _ T M g A t c c18 c19a hK
  obtain ⟨h6b, h6c, h7⟩ := h G T M g A t c c18 c19a hK
  exact ⟨c.centralizer_kOf_eq_bot c18.b, c.normalizer_kOf_eq c18.b c19a hK, h6b, h6c, h7⟩

end S143

end CFSG.Quasithin
