module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormGe
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormF4Defs

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem excCoreNormalizer_of_simplyLaced {m : Fin 6} {τ : Tag} (hm : 2 ≤ m.val)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hsep : ExcRaw.RootSep m) :
    ExcCoreNormalizer m τ := by
  intro L _ _ p S hS T₀ d c hc
  have hN : ExcRaw.normalizerGroup m c = ExcRaw.weyl m c := by
    rw [ExcRaw.normalizerGroup, if_neg fun h => absurd h.1 (by omega)]
  rw [hN]
  exact le_antisymm (d.map_ggAutomizer_codeComponent_le_weyl hsep hc.1)
    (d.weyl_le_map_ggAutomizer_codeComponent hS hτ hm hc)

theorem excCoreNormalizer_E7 : ExcCoreNormalizer 4 .E7 :=
  excCoreNormalizer_of_simplyLaced (by decide) (Or.inr (Or.inl rfl)) ExcRaw.rootSep_four

theorem excCoreNormalizer_E8 : ExcCoreNormalizer 5 .E8 :=
  excCoreNormalizer_of_simplyLaced (by decide) (Or.inr (Or.inr rfl)) ExcRaw.rootSep_five

theorem excCoreNormalizer_E6_two : ExcCoreNormalizer 2 .E6 :=
  excCoreNormalizer_of_simplyLaced (by decide) (Or.inl rfl) ExcRaw.rootSep_two

theorem excCoreNormalizer_E6_three : ExcCoreNormalizer 3 .E6 :=
  excCoreNormalizer_of_simplyLaced (by decide) (Or.inl rfl) ExcRaw.rootSep_three

theorem excCoreNormalizer_F4_of_inputs (hB2 : ExcF4NormB2) (hRW : ExcF4NormRootWeyl) :
    ExcCoreNormalizer 0 .F4 := by
  intro L _ _ p S hS T₀ d c hc
  by_cases h4 : c.card = 4
  · rw [ExcRaw.normalizerGroup, if_pos ⟨rfl, h4⟩]
    exact hB2 S hS d c hc h4
  · rw [ExcRaw.normalizerGroup, if_neg fun h => h4 h.2]
    refine le_antisymm (d.map_ggAutomizer_codeComponent_le_weyl ExcRaw.rootSep_zero hc.1) ?_
    rw [ExcRaw.weyl, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact d.reflection_mem_map_ggAutomizer_of_mem hS i (hRW S hS d c hc h4 i hi)

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
