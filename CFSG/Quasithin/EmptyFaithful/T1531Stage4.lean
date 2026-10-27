module

public import CFSG.Quasithin.EmptyFaithful.T1531Stage3
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Res15362 {G : Type} [Group G] (T Mc M : Subgroup G) : Prop where
  transitive : ∀ g₁ g₂ : G, quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) g₁ →
    quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) g₂ →
      ∃ c ∈ Mc, conjSubgroup (conjSubgroup (VZ T M) g₁) c = conjSubgroup (VZ T M) g₂
  commutes : ∀ g : G, VZ T M ⊓ conjSubgroup (VZ T M) g ≠ ⊥ →
    ⁅VZ T M, conjSubgroup (VZ T M) g⁆ = ⊥

@[expose] def Stage15362 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15350 T M →
      Res15362 T Mc M

@[expose] def Res15363 {G : Type} [Group G] (T M : Subgroup G) : Prop :=
  (3 : ℕ∞) ≤ E3.rParam (VZ T M) →
    E3.wClos (VZ T M) 1 T ≤ Subgroup.centralizer (VZ T M : Set G) ∧
      1 < E3.wParam T (VZ T M) ∧ ∀ H : Subgroup G, IsHTM153 T M H → 1 < E1.nParam H

@[expose] def Stage15363 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15350 T M →
      Res15362 T Mc M → Res15363 T M

@[expose] def Res15364 {G : Type} [Group G] [Finite G] (T Mc M V₁ : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsHTM153 T M H →
    ∀ hF : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H,
      qInt (tildeOf (quasithinOmegaOneCenter T) H)
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure (ZS153 T M V₁) H))
        hF.isElemAbelian_tilde ≤ 2

@[expose] def Res15365One {G : Type} [Group G] (T M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsHStar T M H → E1.nParam H = 1

@[expose] def Stage15365One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15350 T M →
      Res15349 T Mc M V₁ → Res15362 T Mc M → Res15363 T M → Res15364 T Mc M V₁ →
        Res15365One T M

@[expose] def Res15365Two {G : Type} [Group G] (T M : Subgroup G) : Prop :=
  E3.rParam (VZ T M) = 2

section Proofs

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem hypF98_of_results (c : Ctx153 G T Mc M V₁ V₂ t) (r47 : Res15347 T M V₁)
    (r62 : Res15362 T Mc M) {H : Subgroup G}
    (hF : HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H) :
    HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H where
  toHypF91 := hF
  weak_f := fun g hg => by
    rw [conjSub_inv_eq_conjSubgroup] at hg ⊢
    refine r62.commutes g ?_
    intro hbot
    have hZ : quasithinOmegaOneCenter T ≤ VZ T M ⊓ conjSubgroup (VZ T M) g :=
      le_inf c.hyp.Z_le_VZ hg
    have hZbot : quasithinOmegaOneCenter T = ⊥ := le_bot_iff.mp (hbot ▸ hZ)
    have h2 := c.hyp.lemma_15_3_2_two.2
    rw [hZbot, Subgroup.card_bot] at h2
    omega
  case_g := Or.inr fun x hx hne g hg => by
    rcases r47 x hx.2 with h0 | h1
    · exact absurd h0 hne
    · rw [conjSub_inv_eq_conjSubgroup] at hg ⊢
      exact h1 g hg

theorem lemma_15_3_64 (c : Ctx153 G T Mc M V₁ V₂ t) (r47 : Res15347 T M V₁)
    (r62 : Res15362 T Mc M) : Res15364 T Mc M V₁ :=
  fun _ _ hF => (hypF98_of_results c r47 r62 hF).F916_3.1

theorem exists_isHStar_of_inH {K : Subgroup G} (hK : InH T K) (hKM : ¬ K ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H := by
  obtain ⟨H, ⟨hH1, hH2⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {H : Subgroup G | InH T H ∧ ¬ H ≤ M} ⟨K, hK, hKM⟩
  refine ⟨H, hH1, hH2, fun Y hY hYH hYM => ?_⟩
  by_contra hne
  exact hmin Y ⟨hY, hYM⟩ (lt_of_le_of_ne hYH hne)

theorem isHTM153_mc (c : Ctx153 G T Mc M V₁ V₂ t) : IsHTM153 T M Mc := by
  refine ⟨inH_of_inM c.hyp.qtfe.inM_mc, fun hle => c.hyp.ne_mc ?_⟩
  exact c.hyp.qtfe.mc_max.2 M c.hyp.inM.1.1 hle

theorem lemma_15_3_65_two (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (r63 : Res15363 T M) (r65 : Res15365One T M) : Res15365Two T M := by
  by_contra hne
  have h2 : (2 : ℕ∞) ≤ E3.rParam (VZ T M) := by
    have := (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr r46.one_lt_r
    simpa [one_add_one_eq_two] using this
  have hlt : (2 : ℕ∞) < E3.rParam (VZ T M) := lt_of_le_of_ne h2 (Ne.symm hne)
  have h3 : (3 : ℕ∞) ≤ E3.rParam (VZ T M) := by
    have := (ENat.add_one_le_iff (by simp : (2 : ℕ∞) ≠ ⊤)).mpr hlt
    have e : (2 : ℕ∞) + 1 = 3 := by norm_num
    rwa [e] at this
  obtain ⟨H, hH⟩ := exists_isHStar_of_inH (isHTM153_mc c).1 (isHTM153_mc c).2
  have h1 := (r63 h3).2.2 H ⟨hH.1, hH.2.1⟩
  rw [r65 H hH] at h1
  exact lt_irrefl _ h1

end Proofs

end CFSG.Quasithin
