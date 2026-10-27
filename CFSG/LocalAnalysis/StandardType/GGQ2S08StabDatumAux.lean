module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] noncomputable def ggQ2s08x1_h {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) : ↥Bs :=
  Additive.toMul (M.model.symm (M.coroot i))

theorem ggQ2s08x1_h_model {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.model (Additive.ofMul (ggQ2s08x1_h M i)) = M.coroot i := by
  simp [ggQ2s08x1_h]

theorem ggQ2s08x1_simple_h {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.simple i (ggQ2s08x1_h M i) = (ggQ2s08x1_h M i)⁻¹ := by
  apply Additive.ofMul.injective
  change Additive.ofMul ((M.simple i) (ggQ2s08x1_h M i)) =
    - Additive.ofMul (ggQ2s08x1_h M i)
  refine M.model.injective ?_
  rw [map_neg, ← ggLin_apply_ofMul (p := 3) M.model (M.simple i)
    (ggQ2s08x1_h M i), ggQ2s08x1_h_model]
  have hs := M.simple_apply i (M.coroot i)
  rw [M.pairing i i, M.isCartan.1 i] at hs
  rw [hs]
  module

theorem ggQ2s08x1_h_mem_L {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    (ggQ2s08x1_h M i : G) ∈ L := by
  have hBs : IsElemAbelian 3 Bs := hS.1.1.tableB_facts.2.1
  have hsimple : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hsimple
  have hhiN : (ggQ2s08x1_h M i : G) ∈ Subgroup.normalizer (L : Set G) := hBsN (ggQ2s08x1_h M i).2
  have hconj : g * (ggQ2s08x1_h M i : G) * g⁻¹ = (ggQ2s08x1_h M i : G)⁻¹ := by
    have h1 := hg (ggQ2s08x1_h M i)
    rw [ggQ2s08x1_simple_h M i] at h1
    exact h1.symm
  have hcomm : g * (ggQ2s08x1_h M i : G) * g⁻¹ * (ggQ2s08x1_h M i : G)⁻¹ ∈ L := by
    have h1 : (ggQ2s08x1_h M i : G) * g⁻¹ * (ggQ2s08x1_h M i : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hhiN g⁻¹).mp (L.inv_mem hgL)
    have h2 := L.mul_mem hgL h1
    convert h2 using 1
    group
  have heq : g * (ggQ2s08x1_h M i : G) * g⁻¹ * (ggQ2s08x1_h M i : G)⁻¹ =
      (ggQ2s08x1_h M i : G) := by
    rw [hconj]
    have h3 : (ggQ2s08x1_h M i : G) ^ 3 = 1 := by
      have := hBs.2 (ggQ2s08x1_h M i) (ggQ2s08x1_h M i).2
      simpa using this
    calc (ggQ2s08x1_h M i : G)⁻¹ * (ggQ2s08x1_h M i : G)⁻¹
        = (ggQ2s08x1_h M i : G)⁻¹ * (ggQ2s08x1_h M i : G)⁻¹ *
            (ggQ2s08x1_h M i : G) ^ 3 := by rw [h3, mul_one]
      _ = (ggQ2s08x1_h M i : G) := by group
  rwa [heq] at hcomm

end CFSG.StandardType

end
