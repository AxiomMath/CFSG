module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoDelta
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LieType.BorelTits.Tits

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

theorem exclA5BlockFor_two_tits :
    ExclA5BlockFor fun S _ => CFSG.Blueprint.ReeTitsModel S .Tits 2 1 := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  obtain ⟨K, V, T₁, T₂, hVK, hV16, -, hΔ, -, hNV, -⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := hΔ.isPGroup_of_le hVK
  have hV0 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV16
    omega
  obtain ⟨S₀, P', hP'top, hNP', -, -, hS₀⟩ :=
    CFSG.LieType.BorelTits.holdsTits_of_reeTitsModel_tits hS V hV0 hV2
  have hU : IsSylowTwoOf (S₀ : Subgroup S) ⊤ := by
    refine ⟨le_top, S₀.isPGroup', ?_⟩
    rw [show ((S₀ : Subgroup S).subgroupOf ⊤).index = (S₀ : Subgroup S).index from
      Subgroup.relIndex_top_right _]
    exact S₀.not_dvd_index
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice S hS _ hU
  have hPs : Group.IsSolvable ↥P' := by
    rcases hlat _ hS₀ with h | h | h | h
    · rw [h]
      have hp : IsPGroup 2 ↥(S₀ : Subgroup S) := S₀.isPGroup'
      have : Group.IsNilpotent ↥(S₀ : Subgroup S) := hp.isNilpotent
      infer_instance
    · rw [h]; exact hHs
    · rw [h]; exact hNs
    · exact absurd h hP'top
  have hKP : K ≤ P' := (hNV ▸ le_sup_left : K ≤ Subgroup.normalizer (V : Set S)).trans hNP'
  have hKs : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKP)
      (Subgroup.inclusion_injective hKP)
  exact hΔ.not_isSolvable hKs

end CFSG.Quasithin.H13.CTK
