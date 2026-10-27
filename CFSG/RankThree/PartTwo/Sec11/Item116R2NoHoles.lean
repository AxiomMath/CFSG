module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2No
public import CFSG.RankThree.PartTwo.Sec11.Item116R1S

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Certified

@[expose] def ResidueTR1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → ResidueR1 G A c a d →
      A ∈ partTwoT G

theorem item116FusionE9Even_of_residueTR1 (hres : ResidueTR1) (h45 : Sec4.Item4_5)
    (h113 : Item113) (hP2b : Item116P2b) (hP2c : Item116P2c) : Item116FusionE9Even := by
  intro G _ _ A c L a R Y h d hdL hWB hirr hRG h3 hsd16 hnd hcase
  have hdc := Item116Fusion.not_mem_zpowers_of_item45 h45 h hdL
  obtain ⟨hclA, htr, hHW⟩ := hnd hdc
  have hcfg : ∀ hR : ResidueR1 G A c a d ∨ ResidueR2 G A c d, ResidueConfig G A c L a R Y d :=
    fun hR =>
    { h.toSec11StdLocal with
      inf_eq_zpowers := hdL
      not_mem_zpowers := hdc
      normalizer_le := hWB
      isIrreducibleOn := hirr
      isSylowOf_top := hRG
      threeElement_centralizes := h3
      mem_sd16 := hsd16
      closure_eq := hclA
      exists_transvection := htr
      conj_mem_of_mem_normalizer := hHW
      residue := hR }
  by_cases hSD : ∃ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))
  · exact (false_of_R2 h45 h113 (hcfg (Or.inr hSD)) h.not_mem_partTwoT_or_mem_partTwoS hSD).elim
  have hEven := hcase.resolve_right hSD
  have hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) := by
    intro w hw
    rcases hsd16 w hw with h1 | h2 | h3' | h4
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd ⟨w, hw, Or.inl h3'⟩ hSD
    · exact absurd ⟨w, hw, Or.inr h4⟩ hSD
  intro w hwW x hxA
  by_contra hwx
  obtain ⟨n, hnW, hnc, hnd', hna⟩ :=
    TheoremO.exists_bcD8_of_not_mem h hdL hWB hirr hdc hD8 hwW hxA hwx
  have hR1 : ResidueR1 G A c a d := ⟨hEven, hD8, n, hnW, hnc, hnd', hna⟩
  rcases h.not_mem_partTwoT_or_mem_partTwoS with hT | hS
  · exact hT (hres G A c L a R Y d (hcfg (Or.inl hR1)) hR1)
  · exact false_of_R1_of_mem_partTwoS h45 hP2b hP2c (hcfg (Or.inl hR1)) hS hR1

theorem item116FusionE9_of_residueTR1 (hres : ResidueTR1) (hcore : Item116P2bCore)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hP2c : Item116P2c) : Item116FusionE9 :=
  item116FusionE9_of_even_of_core
    (item116FusionE9Even_of_residueTR1 hres h45 h113 (item116P2b_of_core h45 hcore) hP2c)
    hcore h45

theorem item116Fusion_of_residueTR1 (hres : ResidueTR1) (hcore : Item116P2bCore)
    (h45 : Sec4.Item4_5) (h113 : Item113) (hP2c : Item116P2c) : Item116Fusion :=
  item116Fusion_of (item116FusionE9_of_residueTR1 hres hcore h45 h113 hP2c)

end Certified

end CFSG.RankThree.PartTwo.Sec11
