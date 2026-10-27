module

public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.Quasithin.QTFE14Cat

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def StageMfExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∃ M : Subgroup G, IsMf T Mc M

@[expose] def StageTheorem1513 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M →
    (Nat.card (VZ T M) = 4 ∧ SixModels G) ∨ IsOFourPlusAction M (VZ T M)

@[expose] def StageTheorem1531 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → ¬ IsOFourPlusAction M (VZ T M)

theorem six_models_of_parts (P1 : StageMfExists) (P2 : StageTheorem1513) (P3 : StageTheorem1531)
    (G : Type) [Group G] [Finite G] (T Mc : Subgroup G) (h : quasithinQTFE14Cat G T Mc) :
    SixModels G := by
  obtain ⟨M, hM⟩ := P1 G T Mc h
  rcases P2 G T Mc M h hM with ⟨-, h6⟩ | h4
  · exact h6
  · exact absurd h4 (P3 G T Mc M h hM)

structure Hyp1421 (G : Type) [Group G] [Finite G] (T M : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  faithful_empty : ∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L
  mc_max : quasithinIsMaxTwoLocal (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
  m_max : IsOrdMaximal T M
  m_greatest : ∀ M' : Subgroup G, InM T M' → OrdLE T M' M
  rank_two : Nat.card (VZ T M) = 4
  aut_top : autOn M (VZ T M) = ⊤
  two_maximal : ∃ M' : Subgroup G, InM T M' ∧ M' ≠ M

@[expose] def StageTheorem14625 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → SixModels G

@[expose] def StageRankTwoHyp1421 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → Nat.card (VZ T M) = 4 → Hyp1421 G T M

@[expose] def StageRankNotTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → Nat.card (VZ T M) ≠ 4 → IsOFourPlusAction M (VZ T M)

theorem stageTheorem1513_of_parts (h14625 : StageTheorem14625) (hR2 : StageRankTwoHyp1421)
    (hR : StageRankNotTwo) : StageTheorem1513 := by
  intro G _ _ T Mc M h hM
  by_cases h4 : Nat.card (VZ T M) = 4
  · exact Or.inl ⟨h4, h14625 G T M (hR2 G T Mc M h hM h4)⟩
  · exact Or.inr (hR G T Mc M h hM h4)

theorem sixModels_iff (G : Type) [Group G] :
    SixModels G ↔
      (Nonempty (G ≃* quasithinJ2) ∨ Nonempty (G ≃* quasithinJ3) ∨
        Nonempty (G ≃* quasithinTrialityD4Two) ∨ Nonempty (G ≃* quasithinTits) ∨
        Nonempty (G ≃* PSU3 3 1) ∨ Nonempty (G ≃* quasithinM12)) := Iff.rfl

end CFSG.Quasithin
