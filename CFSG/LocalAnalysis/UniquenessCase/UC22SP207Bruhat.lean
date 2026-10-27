module

public import CFSG.GroupTheory.TitsSystem.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.BNPair
open CFSG.GroupTheory.TitsSystem (IsBNPair)
open scoped Pointwise

theorem uc22sp207_dc_mul_subset {X : Type} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
    {S : Set (WeylGroup B N)} (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {a : WeylGroup B N} (ha : a ∈ Subgroup.closure J) (w : WeylGroup B N) :
    dc B N a * dc B N w ⊆ ⋃ v ∈ Subgroup.closure J, dc B N (v * w) := by
  have key : ∀ s ∈ J, ∀ a' : WeylGroup B N,
      dc B N a' * dc B N w ⊆ ⋃ v ∈ Subgroup.closure J, dc B N (v * w) →
      dc B N (s * a') * dc B N w ⊆ ⋃ v ∈ Subgroup.closure J, dc B N (v * w) := by
    intro s hs a' ih
    calc dc B N (s * a') * dc B N w ⊆ dc B N s * dc B N a' * dc B N w :=
          Set.mul_subset_mul_right (dc_mul_subset_of s a')
      _ = dc B N s * (dc B N a' * dc B N w) := mul_assoc _ _ _
      _ ⊆ dc B N s * ⋃ v ∈ Subgroup.closure J, dc B N (v * w) := Set.mul_subset_mul_left ih
      _ = ⋃ v ∈ Subgroup.closure J, dc B N s * dc B N (v * w) := Set.mul_iUnion₂ _ _
      _ ⊆ ⋃ v ∈ Subgroup.closure J, dc B N (v * w) := by
        refine Set.iUnion₂_subset fun v hv => ?_
        refine (h.bnCore.mul_subset s (hJ hs) (v * w)).trans (Set.union_subset ?_ ?_)
        · rw [← mul_assoc]
          exact Set.subset_iUnion₂ (s := fun v (_ : v ∈ Subgroup.closure J) => dc B N (v * w))
            (s * v) (mul_mem (subset_closure hs) hv)
        · exact Set.subset_iUnion₂ (s := fun v (_ : v ∈ Subgroup.closure J) => dc B N (v * w))
            v hv
  induction ha using Subgroup.closure_induction_left with
  | one =>
    intro x hx
    rw [dc_one] at hx
    obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_mul.1 hx
    refine Set.mem_iUnion₂.2 ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    simpa using mul_mem_dc hy hb B.one_mem
  | mul_left s hs a' _ ih => exact key s hs a' ih
  | inv_mul_cancel s hs a' _ ih =>
    rw [h.bnCore.inv_eq (hJ hs)]
    exact key s hs a' ih

theorem uc22sp207_exists_inv_mul_mem_conj {X : Type} [Group X] {B N : Subgroup X}
    [(cartan B N).Normal] {S : Set (WeylGroup B N)} (h : IsBNPair B N S) {U : Subgroup X}
    (hBU : B ≤ normalizer (U : Set X)) (hBUH : B ≤ U ⊔ (B ⊓ N)) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {n₀ : N}
    (hc : ∀ v ∈ Subgroup.closure J,
      (n₀ : WeylGroup B N)⁻¹ * v * (n₀ : WeylGroup B N) ∈ Subgroup.closure J)
    {x : X} (hx : x ∈ parabolic B N J) :
    ∃ u ∈ U, u⁻¹ * x ∈ (parabolic B N J).map (MulAut.conj (n₀ : X)).toMonoidHom := by
  obtain ⟨a, ha, hxa⟩ := (h.mem_parabolic_iff hJ).1 hx
  have hxn : x * (n₀ : X) ∈ dc B N a * dc B N (n₀ : WeylGroup B N) :=
    Set.mul_mem_mul hxa (coe_mem_dc n₀)
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.1 (uc22sp207_dc_mul_subset h hJ ha _ hxn)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective
    ((n₀ : WeylGroup B N)⁻¹ * v * (n₀ : WeylGroup B N))
  have hlift : ((n₀ * m : N) : WeylGroup B N) = v * (n₀ : WeylGroup B N) := by
    rw [QuotientGroup.mk_mul, hm]
    group
  obtain ⟨b, hb, b', hb', hxeq⟩ := (mem_dc_of_lift hlift).1 hxv
  have hbU : b ∈ ((U ⊔ (B ⊓ N) : Subgroup X) : Set X) := hBUH hb
  rw [coe_mul_of_right_le_normalizer_left U (B ⊓ N) (inf_le_left.trans hBU)] at hbU
  obtain ⟨u, hu, t, ht, rfl⟩ := Set.mem_mul.1 hbU
  have ht' : t ∈ B ⊓ N := ht
  have hmJ : (m : WeylGroup B N) ∈ Subgroup.closure J := hm ▸ hc v hv
  refine ⟨u, hu, (n₀ : X)⁻¹ * t * n₀ * ((m : X) * b'), mul_mem ?_ ?_, ?_⟩
  · have hmem : (⟨t, (mem_inf.1 ht').2⟩ : N) ∈ (B ⊓ N).subgroupOf N := mem_subgroupOf.2 ht'
    have hconj := (inferInstance : ((B ⊓ N).subgroupOf N).Normal).conj_mem _ hmem n₀⁻¹
    rw [inv_inv, mem_subgroupOf] at hconj
    exact h.le_parabolic hJ (mem_inf.1 hconj).1
  · exact h.dc_subset_parabolic hJ hmJ
      ((mem_dc_mk_iff (n := m)).2 ⟨1, B.one_mem, b', hb', by simp⟩)
  · have hx' : x = u * t * ((n₀ : X) * m) * b' * (n₀ : X)⁻¹ := by
      rw [← mul_inv_cancel_right x (n₀ : X), hxeq]
      simp [mul_assoc]
    rw [hx']
    simp [MulAut.conj_apply, mul_assoc]

end CFSG.LocalAnalysis.UniquenessCase.UC22
