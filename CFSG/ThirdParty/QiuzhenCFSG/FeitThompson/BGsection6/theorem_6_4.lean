module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_3_a_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # Theorem 6.4 from BG Section 6 -/

public theorem CFSG.conjBy_eq_of_mem_normalizer_local
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (G := G) H) :
    H.conjBy g = H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    simpa [Subgroup.conjBy, MulAut.conj_apply, mul_assoc] using
      ((Subgroup.mem_normalizer_iff).1 hg y).1 hy
  · intro hx
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have hgInv : g⁻¹ ∈ Subgroup.normalizer (G := G) H :=
        (Subgroup.normalizer (G := G) (H : Set G)).inv_mem hg
      simpa [mul_assoc] using ((Subgroup.mem_normalizer_iff).1 hgInv x).1 hx
    · simp [MulAut.conj_apply, mul_assoc]

public theorem CFSG.mem_normalizer_of_conjBy_eq_local
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (G := G) H := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      refine Subgroup.mem_map.mpr ?_
      exact ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (MulAut.conj g y) * g := by rw [← hyx]; rfl
        _ = y := by simp [MulAut.conj_apply, mul_assoc]
    simpa [this] using hy


universe u64


