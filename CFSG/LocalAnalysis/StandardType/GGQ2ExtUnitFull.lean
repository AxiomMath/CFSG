module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtClassicalStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusChainA
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitShapes
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalInsideMoved

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem extCasesUnitFull_of_chain : ExtCasesUnitFull := by
  have hc := unitFullChainLeaf_holds
  intro N vx hvx0 ℓ hadm _ hocc hcent _ U _ _ j _ _ _ _ _ z _ hzvx k hcand _
  obtain ⟨-, hkocc, hkcent, -, -⟩ := hcand
  have hz0 : z ≠ 0 := fun h0 => hzvx (h0 ▸ Submodule.zero_mem _)
  obtain ⟨a, s, hs, hvxa, hℓ⟩ := UnitRaw.lineShapes_holds N vx ℓ hvx0 hocc hcent
  obtain ⟨c, s', hs', hzc, hk⟩ := UnitRaw.lineShapes_holds N z k hz0 hkocc hkcent
  have hac : a ≠ c := by
    rintro rfl
    have key : (s' * s⁻¹) • (s • UnitRaw.unitVec N a) = s' • UnitRaw.unitVec N a := by
      rw [← mul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one]
    refine hzvx (Submodule.mem_span_singleton.mpr ⟨s' * s⁻¹, ?_⟩)
    rw [hvxa, hzc]
    exact key
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by have := hadm.1; omega⟩
  subst hℓ hk
  exact Or.inr (Or.inr (Or.inl (hc n (by have := hadm.1; omega) a c hac vx z hcent hkcent)))

theorem extCasesUnitFull_holds : ExtCasesUnitFull :=
  extCasesUnitFull_of_chain

end CFSG.StandardType.GGQ2Frame

end
