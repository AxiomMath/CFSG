module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace S15223P4

namespace B

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem lnQuot_of_autOn (hcover : AsA36NoOddCover) (c : P4Ctx T Mc M H B₀ I X)
    (h : Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥(autOn X (P4V M I X)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))))
    (hB : ¬ IsBorelIn (autOn X (P4V M I X)) (autOn (MX M I X) (P4V M I X))) :
    IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5 := by
  have hLN := X_le_normalizer_V c
  have hker := pCoreOf_X_le_centralizer_V c
  have hnt : ¬ X ≤ Subgroup.centralizer (P4V M I X : Set G) := by
    intro hc
    have h0 : autOn X (P4V M I X) = ⊥ := autOn_eq_bot_of_le_centralizer hc
    have h1 : autOn (MX M I X) (P4V M I X) = ⊥ :=
      le_bot_iff.1 (h0 ▸ autOn_le_autOn _ (inf_le_right : MX M I X ≤ X))
    refine hB ⟨⊥, ?_, ?_⟩
    · rw [h0]
      exact ⟨le_rfl, by simp [IsPGroup], by simp⟩
    · rw [h0, h1]
      simp
  have hsq : SQTKGroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    S153D.sqtkGroup_quot_pCore (B5.sqtk_of_le c.hyp.sqtk c.X_le_I)
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hH : IsL345Type ↥(autOn X (P4V M I X)) :=
      Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨e⟩⟩)
    obtain ⟨e'⟩ := S153D.nonempty_quot_mulEquiv_autOn hcover hLN c.quasi hsq hker hnt hH
    exact Or.inl ⟨e'.trans e⟩
  · have hH : IsL345Type ↥(autOn X (P4V M I X)) :=
      Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨e⟩⟩)
    obtain ⟨e'⟩ := S153D.nonempty_quot_mulEquiv_autOn hcover hLN c.quasi hsq hker hnt hH
    exact Or.inr ⟨e'.trans e⟩

end B

end S15223P4

end CFSG.Quasithin
