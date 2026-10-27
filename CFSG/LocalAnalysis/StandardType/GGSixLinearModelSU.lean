module

public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUField
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelRest

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggSixLinearTorusModelV2On_PSU : GGSixLinearTorusModelV2On .PSU := by
  intro G _ _ p Bs G₀ n f ψ hS hlin _ hyex
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hpq : p ∣ 2 ^ f + 1 := by
    rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by decide)
    · exact h
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hS.2.1
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hrange
  exact SUModel.torusModel_of_su hS.prime hp5 hnp hpq hker hS.2.2.1 hS.bstar_le hS.elem
    hS.2.2.2.1.2.2 hS.omega hS.unique hS.normalizer_le
    (fun hpf y hy hyp => SUModel.exists_mem_suInducedPairs_of_dvd hS.prime hp5 hnp hpq hpf hker
      hS.2.2.1 hS.bstar_le hS.elem hS.2.2.2.1.2.2 hS.omega hS.unique hy hyp) hyex

theorem ggSixLSixTwelveInput_holds : GGSixLSixTwelveInput :=
  ggSixLSixTwelveInput_of_psu_torus ggSixLinearTorusModelV2On_PSU

end Inputs

end CFSG.StandardType
