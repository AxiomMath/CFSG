module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelAbs
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.QuasithinUnique.Borel252

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

section Borel

variable {M : Type} [Group M] {U R₁ R₂ : Subgroup M}

theorem BorelData.not_norm_le₁ (h : BorelData M U R₁ R₂) :
    ¬ Subgroup.normalizer (R₁ : Set M) ≤ Subgroup.normalizer (R₂ : Set M) := by
  intro h12
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set M) :=
    Subgroup.le_normalizer.trans h.lt₁.le
  have hR : R₂ ≤ R₁ := by
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le₂.trans hUN₁) h12 h.isPGroup₂
    rwa [h.core₁] at this
  have hUR : U = R₁ := by
    rw [← h.sup]
    exact sup_eq_left.mpr hR
  exact h.lt₁.ne (by rw [hUR])

theorem BorelData.not_norm_le₂ (h : BorelData M U R₁ R₂) :
    ¬ Subgroup.normalizer (R₂ : Set M) ≤ Subgroup.normalizer (R₁ : Set M) := by
  intro h21
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set M) :=
    Subgroup.le_normalizer.trans h.lt₂.le
  have hR : R₁ ≤ R₂ := by
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.le₁.trans hUN₂) h21 h.isPGroup₁
    rwa [h.core₂] at this
  have hUR : U = R₂ := by
    rw [← h.sup]
    exact sup_eq_right.mpr hR
  exact h.lt₂.ne (by rw [hUR])

theorem BorelData.inf_norm (h : BorelData M U R₁ R₂) :
    Subgroup.normalizer (R₁ : Set M) ⊓ Subgroup.normalizer (R₂ : Set M) =
      Subgroup.normalizer (U : Set M) := by
  apply le_antisymm
  · by_contra hne
    have hlt : Subgroup.normalizer (U : Set M) <
        Subgroup.normalizer (R₁ : Set M) ⊓ Subgroup.normalizer (R₂ : Set M) :=
      lt_of_le_of_ne (le_inf h.lt₁.le h.lt₂.le) (fun heq => hne heq.symm.le)
    have hlt' : Subgroup.normalizer (R₁ : Set M) ⊓ Subgroup.normalizer (R₂ : Set M) < ⊤ :=
      lt_of_le_of_lt inf_le_left h.lt_top₁
    rcases h.only _ hlt hlt' with e | e
    · exact h.not_norm_le₁ (e ▸ inf_le_right)
    · exact h.not_norm_le₂ (e ▸ inf_le_left)
  · exact le_inf h.lt₁.le h.lt₂.le

theorem BorelData.ne_bot₁ (h : BorelData M U R₁ R₂) : R₁ ≠ ⊥ := by
  intro hR
  have : Subgroup.normalizer (R₁ : Set M) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr (by rw [hR]; exact Subgroup.normal_bot)
  exact absurd this h.lt_top₁.ne

theorem BorelData.ne_bot₂ (h : BorelData M U R₁ R₂) : R₂ ≠ ⊥ := by
  intro hR
  have : Subgroup.normalizer (R₂ : Set M) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr (by rw [hR]; exact Subgroup.normal_bot)
  exact absurd this h.lt_top₂.ne

theorem BorelData.isMaximalTwoLocal₁ (h : BorelData M U R₁ R₂)
    (hO2 : ∀ P : Subgroup M, P.Normal → IsPGroup 2 P → P = ⊥) :
    CFSG.Quasithin.IsMaximalTwoLocal (Subgroup.normalizer (R₁ : Set M)) := by
  refine ⟨⟨R₁, h.ne_bot₁, h.isPGroup₁, rfl⟩, fun M' hM' hle => ?_⟩
  obtain ⟨P', hP'ne, hP'p, rfl⟩ := hM'
  by_cases htop : Subgroup.normalizer (P' : Set M) = ⊤
  · exact absurd (hO2 P' (Subgroup.normalizer_eq_top_iff.mp htop) hP'p) hP'ne
  · have hlt : Subgroup.normalizer (P' : Set M) < ⊤ := lt_top_iff_ne_top.mpr htop
    rcases h.only _ (lt_of_lt_of_le h.lt₁ hle) hlt with e | e
    · exact e
    · exact absurd (e ▸ hle) h.not_norm_le₁

theorem BorelData.isMaximalTwoLocal₂ (h : BorelData M U R₁ R₂)
    (hO2 : ∀ P : Subgroup M, P.Normal → IsPGroup 2 P → P = ⊥) :
    CFSG.Quasithin.IsMaximalTwoLocal (Subgroup.normalizer (R₂ : Set M)) := by
  refine ⟨⟨R₂, h.ne_bot₂, h.isPGroup₂, rfl⟩, fun M' hM' hle => ?_⟩
  obtain ⟨P', hP'ne, hP'p, rfl⟩ := hM'
  by_cases htop : Subgroup.normalizer (P' : Set M) = ⊤
  · exact absurd (hO2 P' (Subgroup.normalizer_eq_top_iff.mp htop) hP'p) hP'ne
  · have hlt : Subgroup.normalizer (P' : Set M) < ⊤ := lt_top_iff_ne_top.mpr htop
    rcases h.only _ (lt_of_lt_of_le h.lt₂ hle) hlt with e | e
    · exact absurd (e ▸ hle) h.not_norm_le₂
    · exact e

theorem BorelData.yam_cases (h : BorelData M U R₁ R₂)
    (hO2 : ∀ P : Subgroup M, P.Normal → IsPGroup 2 P → P = ⊥) {P₁ P₂ : Subgroup M}
    (hy : CFSG.Quasithin.IsYAmalgamPair U P₁ P₂) :
    (P₁ = Subgroup.normalizer (R₁ : Set M) ∧ P₂ = Subgroup.normalizer (R₂ : Set M)) ∨
      (P₁ = Subgroup.normalizer (R₂ : Set M) ∧ P₂ = Subgroup.normalizer (R₁ : Set M)) := by
  obtain ⟨-, -, hiff⟩ := hy
  have h1 := (hiff _).mp ⟨h.isMaximalTwoLocal₁ hO2, h.lt₁.le⟩
  have h2 := (hiff _).mp ⟨h.isMaximalTwoLocal₂ hO2, h.lt₂.le⟩
  have hne := h.ne_norm
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩
  · exact absurd (h1.trans h2.symm) hne

end Borel

end CFSG.QuasithinUnique.Borel252
