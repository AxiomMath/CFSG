module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs

import CFSG.LieType.Steinberg.TwistedE6.Roots

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section TwClass

theorem ggTwClass
    (β : Fin (Tag.rank .F4) → ℤ) (hβ : IsRoot .F4 β) :
    ∃ a : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 a ∧
      (∀ α : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 α →
        ((∃ c : ℕ, 0 < c ∧ orbitSum orbitMap α = c • β) ↔ α = a ∨ α = rho a)) ∧
      (rho a = a ∨ (¬ IsRoot .E6 (a + rho a) ∧ a + rho a ≠ 0)) := by
  obtain ⟨a, ha, hproj⟩ := CFSG.LieType.Steinberg.TwistedE6.exists_proj_eq hβ
  refine ⟨a, ha, ?_, ?_⟩
  · intro α hα
    constructor
    · rintro ⟨c, hc, hcβ⟩
      have hprojα : CFSG.LieType.Steinberg.TwistedE6.proj α =
          c • CFSG.LieType.Steinberg.TwistedE6.proj a := by
        rw [CFSG.LieType.Steinberg.TwistedE6.proj_apply, hcβ, ← hproj]
      have hc1 : c = 1 :=
        CFSG.LieType.Steinberg.TwistedE6.eq_one_of_proj_eq_nsmul hα ha hc hprojα
      have hproj' : CFSG.LieType.Steinberg.TwistedE6.proj α =
          CFSG.LieType.Steinberg.TwistedE6.proj a := by
        rw [hc1] at hprojα
        simpa using hprojα
      exact (CFSG.LieType.Steinberg.TwistedE6.proj_eq_proj_iff ha hα).1 hproj'.symm
    · rintro (rfl | rfl)
      · exact ⟨1, Nat.one_pos, by
          rw [← CFSG.LieType.Steinberg.TwistedE6.proj_apply, hproj, one_smul]⟩
      · exact ⟨1, Nat.one_pos, by
          rw [← CFSG.LieType.Steinberg.TwistedE6.proj_apply,
            CFSG.LieType.Steinberg.TwistedE6.proj_rho, hproj, one_smul]⟩
  · by_cases h : rho a = a
    · exact Or.inl h
    · exact Or.inr ⟨CFSG.LieType.Steinberg.TwistedE6.not_isRoot_add_rho ha h,
        CFSG.LieType.Steinberg.TwistedE6.add_rho_ne_zero ha h⟩

end TwClass

end CFSG.StandardType.GGFinModel
