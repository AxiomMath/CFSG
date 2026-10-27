module

public import CFSG.Sporadic.Schreier.LyGeneration
public import CFSG.Sporadic.Schreier.LyR3EFilters

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.SchreierLemmas

theorem eq_top_of_conj_lyf
    {L : Subgroup J} (hCL : lyC ≤ L)
    (hfz : ∃ l ∈ L, l * lyz * l⁻¹ = lyf) :
    L = ⊤ ∧ ∀ t ∈ L, orderOf t = 2 → ∃ l ∈ L, l * lyz * l⁻¹ = t := by
  have hSL : (lySylow : Subgroup J) ≤ L := le_trans lyS_le_lyC hCL
  have hCL' : Subgroup.centralizer {lyz} ≤ L := by
    rw [← full_involution_centralizer.1]; exact hCL
  have hconj : ∀ t ∈ L, orderOf t = 2 → ∃ l ∈ L, l * lyz * l⁻¹ = t := by
    intro t htL ht2
    obtain ⟨l, hl, hlt⟩ : ∃ l ∈ L, l * t * l⁻¹ ∈ lyS := by
      have hp : IsPGroup 2 (Subgroup.zpowers (⟨t, htL⟩ : ↥L)) := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
        exact ht2
      obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L Q (lySylow.subtype hSL)
      have hmem := Subgroup.smul_mem_pointwise_smul (⟨t, htL⟩ : ↥L) (MulAut.conj g)
        (Q : Subgroup ↥L) (hQ (Subgroup.mem_zpowers _))
      rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
      refine ⟨g, g.2, ?_⟩
      simpa [MulAut.smul_def, lySylow_coe] using hmem
    have hs2 : orderOf (l * t * l⁻¹) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj l) t
      rw [MulAut.conj_apply] at this
      rw [this, ht2]
    by_cases hc : ∀ x ∈ lyS, x * (l * t * l⁻¹) = (l * t * l⁻¹) * x
    ·
      have hcen : (⟨l * t * l⁻¹, hlt⟩ : lyS) ∈ Subgroup.center lyS := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hc g.1 g.2
      rw [center_lyS, mem_zpowers_zS] at hcen
      rcases hcen with h | h
      · exfalso
        have h0 := congrArg Subtype.val h
        rw [Subgroup.coe_one] at h0
        have h1 : l * t * l⁻¹ = 1 := h0
        rw [h1, orderOf_one] at hs2
        exact absurd hs2 (by norm_num)
      · have h0 := congrArg Subtype.val h
        have h1 : l * t * l⁻¹ = lyz := h0
        refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
        rw [← h1]
        group
    · obtain ⟨c, hcC, hcs⟩ := conj_to_f hlt hs2 hc
      obtain ⟨n, hnL, hnz⟩ := hfz
      refine ⟨l⁻¹ * c * n, L.mul_mem (L.mul_mem (L.inv_mem hl) (hCL hcC)) hnL, ?_⟩
      calc l⁻¹ * c * n * lyz * (l⁻¹ * c * n)⁻¹ = l⁻¹ * (c * (n * lyz * n⁻¹) * c⁻¹) * l := by
            group
        _ = l⁻¹ * (l * t * l⁻¹) * l := by rw [hnz, hcs]
        _ = t := by group
  have key := involution_coset_index_generation (G := J) lySylow (by exact hSL) (by exact hCL')
    (by exact hconj)
  have hS : Nat.card ↥(lySylow : Subgroup J) = 256 := card_lyS
  refine ⟨key.2.2 fun d hd hdvd hmod => divisor_check d hd ?_ ?_, hconj⟩
  · rwa [index_centralizer_lyz] at hdvd
  · rwa [hS] at hmod

theorem involution_centralizer_fusion_generator :
    Subgroup.closure ((lyC : Set J) ∪ {r3eG}) = ⊤ ∧
    ∀ t : J, orderOf t = 2 → ∃ x : J, x * lyz * x⁻¹ = t := by
  have hCL : lyC ≤ Subgroup.closure ((lyC : Set J) ∪ {r3eG}) :=
    fun c hc => Subgroup.subset_closure (Or.inl hc)
  have hgL : r3eG ∈ Subgroup.closure ((lyC : Set J) ∪ {r3eG}) :=
    Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨htop, hconj⟩ := eq_top_of_conj_lyf hCL ⟨r3eG, hgL, r3eG_conj_lyz⟩
  refine ⟨htop, fun t ht => ?_⟩
  obtain ⟨l, -, hl⟩ := hconj t (by rw [htop]; exact Subgroup.mem_top t) ht
  exact ⟨l, hl⟩

end CFSG.Sporadic.LySchreier
