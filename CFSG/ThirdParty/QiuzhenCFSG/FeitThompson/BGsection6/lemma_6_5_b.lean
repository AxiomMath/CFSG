module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_5_a

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # Lemma 6.5(b) from BG Section 6 -/

public theorem CFSG.lemma_6_5_b
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {K U H : Subgroup G} [K.Normal] (hKU : K ⊔ U = ⊤) (hHU : H ≤ U)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    (Subgroup.normalizer (G := G) H : Set G) =
      (subgroupCentralizerIn K H) * (subgroupNormalizerIn U H) := by
  classical
  ext g
  constructor
  · intro hgN
    have hconj_le_U : H.conjBy g ≤ U := by
      intro x hx
      have hxH : x ∈ H := by
        simpa [lemma_6_5_conjBy_eq_of_mem_normalizer (H := H) hgN] using hx
      exact hHU hxH
    obtain ⟨c, hcC, u, huU, hguc⟩ :=
      lemma_6_5_c_core (K := K) (U := U) (H := H) hKU hHU hcop g hconj_le_U
    have huN : u ∈ subgroupNormalizerIn U H := by
      have hcN : c ∈ Subgroup.normalizer (G := G) H :=
        lemma_6_5_centralizerIn_le_normalizer K H hcC
      have hcInvN : c⁻¹ ∈ Subgroup.normalizer (G := G) H :=
        (Subgroup.normalizer (G := G) (H : Set G)).inv_mem hcN
      have hu_eq : u = g * c⁻¹ := by
        rw [hguc]
        group
      refine ⟨?_, huU⟩
      rw [hu_eq]
      exact (Subgroup.normalizer (G := G) (H : Set G)).mul_mem hgN hcInvN
    have hc_for_product : u * c * u⁻¹ ∈ subgroupCentralizerIn K H := by
      refine ⟨?_, ?_⟩
      · exact (inferInstance : K.Normal).conj_mem c hcC.1 u
      · change u * c * u⁻¹ ∈ Subgroup.centralizer (H : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have huInvN : u⁻¹ ∈ Subgroup.normalizer (G := G) H :=
          (Subgroup.normalizer (G := G) (H : Set G)).inv_mem huN.1
        have huhu : u⁻¹ * h * u ∈ H := by
          simpa [mul_assoc] using ((Subgroup.mem_normalizer_iff).1 huInvN h).1 hh
        have hcomm : (u⁻¹ * h * u) * c = c * (u⁻¹ * h * u) :=
          (Subgroup.mem_centralizer_iff.mp hcC.2) (u⁻¹ * h * u) huhu
        calc
          h * (u * c * u⁻¹) = u * ((u⁻¹ * h * u) * c) * u⁻¹ := by group
          _ = u * (c * (u⁻¹ * h * u)) * u⁻¹ := by rw [hcomm]
          _ = (u * c * u⁻¹) * h := by group
    have hmem :
        g ∈ (subgroupCentralizerIn K H : Set G) *
            (subgroupNormalizerIn U H : Set G) := by
      refine ⟨u * c * u⁻¹, hc_for_product, u, huN, ?_⟩
      rw [hguc]
      group
    exact hmem
  · intro hg
    have hnorm : g ∈ Subgroup.normalizer (G := G) H := by
      rcases hg with ⟨c, hcC, u, huN, hcu⟩
      rw [← hcu]
      exact (Subgroup.normalizer (G := G) (H : Set G)).mul_mem
        (lemma_6_5_centralizerIn_le_normalizer K H hcC) huN.1
    exact hnorm
