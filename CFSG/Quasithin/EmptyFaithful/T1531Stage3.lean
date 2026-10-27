module

public import CFSG.Quasithin.EmptyFaithful.T1531Stage2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Cases

variable {G : Type} [Group G] {T Mc M : Subgroup G}

theorem not_case157Two_of_case157One (h : Case157One T Mc M) : ¬ Case157Two T Mc M := by
  rintro ⟨hp, -⟩
  obtain ⟨e⟩ := h.2
  have h9 : Nat.card (OTwoQuot (Y153 Mc M)) = 9 := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))]
    simp
  have h27 := hp.2.1
  rw [h9] at h27
  norm_num at h27

end Cases

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem hypF91_of_stage15348 (h48 : Stage15348) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂) (r47 : Res15347 T M V₁)
    (r49 : Res15349 T Mc M V₁) {H : Subgroup G} (hH : IsHTM153 T M H) :
    HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H :=
  h48 G T Mc M V₁ V₂ t c r45 r46 r47 H hH
    (fun h2 => absurd h2 (not_case157Two_of_case157One r49.case_one))

@[expose] def Res15350 {G : Type} [Group G] (T M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsHTM153 T M H →
    ∀ a ∈ conjClosure (VZ T M) H, ∀ b ∈ conjClosure (VZ T M) H, a * b = b * a

@[expose] def Stage15350 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15347 T M V₁ →
      Res15349 T Mc M V₁ →
      (∀ H : Subgroup G, IsHTM153 T M H →
        HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H) →
      Res15350 T M

end CFSG.Quasithin
