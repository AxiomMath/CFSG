module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Comp
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

theorem normal_ker_components (N : Type) [Group N] :
    (⨅ J : {J : Subgroup N // CFSG.IsComponent J}, Subgroup.normalizer (J.1 : Set N)).Normal := by
  refine ⟨fun k hk g => ?_⟩
  rw [Subgroup.mem_iInf] at hk ⊢
  intro J
  have hJ'c : CFSG.IsComponent (J.1.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) J.2
  have e2 := Subgroup.mem_normalizer_iff.mp (hk ⟨_, hJ'c⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e1 : g⁻¹ * x * g ∈ J.1.map (MulAut.conj g⁻¹).toMonoidHom ↔ x ∈ J.1 := by
    rw [r3c_conj_mem_map_iff]
    have : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [this]
  have e3 : k * (g⁻¹ * x * g) * k⁻¹ ∈ J.1.map (MulAut.conj g⁻¹).toMonoidHom ↔
      g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ ∈ J.1 := by
    rw [r3c_conj_mem_map_iff]
    have : (g⁻¹)⁻¹ * (k * (g⁻¹ * x * g) * k⁻¹) * g⁻¹ = g * k * g⁻¹ * x * (g * k * g⁻¹)⁻¹ := by
      group
    rw [this]
  rw [← e1, ← e3]
  exact e2 (g⁻¹ * x * g)

end CFSG.RankThree.PartTwo.Sec13.F135Last
