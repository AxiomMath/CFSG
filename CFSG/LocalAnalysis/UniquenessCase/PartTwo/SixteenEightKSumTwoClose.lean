module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_sum_two_models (h : S16gRowCtx D V₀ V L hV) {D₁ D₂ : FFModel}
    {I₁ I₂ : Subgroup (Vtil V₀ V hV)} {π₁ : D₁.Gam →* ↥(lBar V₀ V hV L)}
    {π₂ : D₂.Gam →* ↥(lBar V₀ V hV L)}
    (hZ₁ : fixV (lBar V₀ V hV L) ≤ I₁) (hZ₂ : fixV (lBar V₀ V hV L) ≤ I₂)
    (hsup : fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) = ⊤)
    (h₁ : D₁.RealizesVia (lBar V₀ V hV L) I₁ (fixV (lBar V₀ V hV L)) π₁)
    (h₂ : D₂.RealizesVia (lBar V₀ V hV L) I₂ (fixV (lBar V₀ V hV L)) π₂)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    (hne : ∃ m : ↥D₁.sec, (m : D₁.Amb) ∉ D₁.ker)
    (hfix : ∀ (m₁ : ↥D₁.sec) (m₂ : ↥D₂.sec),
      ((m₁ : D₁.Amb) ∉ D₁.ker ∨ (m₂ : D₂.Amb) ∉ D₂.ker) →
      ∃ B : Subgroup ↥(lBar V₀ V hV L), IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B,
        (∃ γ : D₁.Gam, π₁ γ = b ∧ D₁.act γ (m₁ : D₁.Amb) * (m₁ : D₁.Amb)⁻¹ ∈ D₁.ker) ∧
        (∃ γ : D₂.Gam, π₂ γ = b ∧ D₂.act γ (m₂ : D₂.Amb) * (m₂ : D₂.Amb)⁻¹ ∈ D₂.ker)) :
    False :=
  s16g_false_of_fix D h.std h.setting hp hpσ
    (s16k_sum_two_transport h hZ₁ hZ₂ hsup h₁ h₂ hp hp2 hne hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
