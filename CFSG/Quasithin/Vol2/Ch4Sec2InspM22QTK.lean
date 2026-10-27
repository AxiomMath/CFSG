module

public import CFSG.LocalAnalysis.SectionRank.QTK.List

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI

theorem untwisted_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (τ : Tag) (q : ℕ)
    (h : UntwistedChevalleyModel G τ q) : UntwistedChevalleyModel G' τ q := by
  obtain ⟨K, hK, hfin, hc, ⟨φ⟩⟩ := h
  exact ⟨K, hK, hfin, hc, ⟨e.symm.trans φ⟩⟩

theorem twisted_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (t : TwistTag) (q : ℕ)
    (h : TwistedChevalleyModel G t q) : TwistedChevalleyModel G' t q := by
  obtain ⟨K, hK, hfin, hc, σ, hσ, ⟨φ⟩⟩ := h
  exact ⟨K, hK, hfin, hc, σ, hσ, ⟨e.symm.trans φ⟩⟩

theorem reeRelation_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (τ : Tag)
    (ρ : Equiv.Perm (Fin τ.rank)) (L : Finset (Fin τ.rank)) (p f a : ℕ)
    (h : ReeTitsRelationModel G τ ρ L p f a) : ReeTitsRelationModel G' τ ρ L p f a := by
  obtain ⟨K, hK, hfin, hc, ⟨φ⟩⟩ := h
  exact ⟨K, hK, hfin, hc, ⟨e.symm.trans φ⟩⟩

theorem chevalley_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {t : StatedLieTag}
    {p f : ℕ} (h : ChevalleyExceptionalModel G t p f) : ChevalleyExceptionalModel G' t p f := by
  obtain ⟨hadm, hm⟩ := h
  refine ⟨hadm, ?_⟩
  cases t
  all_goals first
    | exact untwisted_mulEquiv e _ _ hm
    | exact twisted_mulEquiv e _ _ hm
    | exact hm

theorem reeTits_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {t : StatedLieTag}
    {p f : ℕ} (h : ReeTitsModel G t p f) : ReeTitsModel G' t p f := by
  obtain ⟨hadm, a, ha, hm⟩ := h
  refine ⟨hadm, a, ha, ?_⟩
  cases t
  all_goals first
    | exact reeRelation_mulEquiv e _ _ _ _ _ _ hm
    | exact hm

theorem suzuki_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {p f : ℕ}
    (h : SuzukiModel G p f) : SuzukiModel G' p f := by
  obtain ⟨hp, a, ha, K, hK, hfin, hf, hc, ⟨φ⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hfin, hf, hc, ⟨e.symm.trans φ⟩⟩

theorem qtkSimpleList_congr {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : QTKSimpleList A) : QTKSimpleList B := by
  unfold QTKSimpleList at h ⊢
  rcases h with h1 | h2 | (h3 | h4 | h5) | (h6 | h7) | h8
  ·
    obtain ⟨n, hn5, hn9, ⟨φ⟩⟩ := h1
    exact Or.inl ⟨n, hn5, hn9, ⟨e.symm.trans φ⟩⟩
  ·
    obtain ⟨p, hp, hp2, hp'⟩ := h2
    right; left
    refine ⟨p, hp, hp2, ?_⟩
    rcases hp' with ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | h | h | ⟨ha, h⟩ | ⟨hb, h⟩
    · left; exact ⟨f, hf, statedClassicalModel_of_mulEquiv e h⟩
    · right; left
      refine ⟨f, hf, ?_⟩
      rcases h with h | h
      · exact Or.inl (statedClassicalModel_of_mulEquiv e h)
      · exact Or.inr (statedClassicalModel_of_mulEquiv e h)
    · right; right; left; exact statedClassicalModel_of_mulEquiv e h
    · right; right; right; left; exact chevalley_mulEquiv e h
    · right; right; right; right; left; exact ⟨ha, statedClassicalModel_of_mulEquiv e h⟩
    · right; right; right; right; right; exact ⟨hb, statedClassicalModel_of_mulEquiv e h⟩
  ·
    obtain ⟨f, hf⟩ := h3
    right; right; left; left
    refine ⟨f, ?_⟩
    rcases hf with ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ |
      ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩
    · left; exact ⟨h1, statedClassicalModel_of_mulEquiv e h⟩
    · right; left; exact ⟨h1, statedClassicalModel_of_mulEquiv e h⟩
    · right; right; left; exact ⟨h1, statedClassicalModel_of_mulEquiv e h⟩
    · right; right; right; left; exact ⟨h1, statedClassicalModel_of_mulEquiv e h⟩
    · right; right; right; right; left; exact ⟨h1, statedClassicalModel_of_mulEquiv e h⟩
    · right; right; right; right; right; left; exact ⟨h1, chevalley_mulEquiv e h⟩
    · right; right; right; right; right; right; left; exact ⟨h1, chevalley_mulEquiv e h⟩
    · right; right; right; right; right; right; right; left
      exact ⟨h1, h2, reeTits_mulEquiv e h⟩
    · right; right; right; right; right; right; right; right
      exact ⟨h1, h2, suzuki_mulEquiv e h⟩
  ·
    right; right; left; right; left
    exact statedClassicalModel_of_mulEquiv e h4
  ·
    right; right; left; right; right
    exact reeTits_mulEquiv e h5
  ·
    obtain ⟨n, hn, h⟩ := h6
    right; right; right; left; left
    exact ⟨n, hn, statedClassicalModel_of_mulEquiv e h⟩
  ·
    right; right; right; left; right
    exact statedClassicalModel_of_mulEquiv e h7
  ·
    obtain ⟨s, hs, ⟨φ⟩⟩ := h8
    right; right; right; right
    exact ⟨s, hs, ⟨e.symm.trans φ⟩⟩

end CFSG.SectionRank.QTK

end
