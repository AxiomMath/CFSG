module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

theorem eq_pCore_of_normal_of_isSimpleGroup {L : Type*} [Group L] {p : ℕ}
    [IsSimpleGroup (L ⧸ CFSG.pCore p L)] {N : Subgroup L} (hN : N.Normal)
    (hON : CFSG.pCore p L ≤ N) (hNt : N ≠ ⊤) : N = CFSG.pCore p L := by
  have := hN.map (QuotientGroup.mk' (CFSG.pCore p L)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore p L)))
    with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact le_antisymm h hON
  · exfalso
    apply hNt
    have h' := comap_map_eq (QuotientGroup.mk' (CFSG.pCore p L)) N
    rw [h, comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hON] at h'
    exact h'.symm

theorem simple_core_quotient_action_kernel {L V : Type*} [Group L] [Group V] {p : ℕ}
    [IsSimpleGroup (L ⧸ CFSG.pCore p L)] (φ : L →* MulAut V)
    (hO : ∀ l ∈ CFSG.pCore p L, ∀ v : V, φ l v = v) (hφ : ∃ l : L, ∃ v : V, φ l v ≠ v) :
    φ.ker = CFSG.pCore p L ∧
      ∃ e : L ⧸ CFSG.pCore p L ≃* φ.range, ∀ l : L, e l = φ.rangeRestrict l := by
  have hker : φ.ker = CFSG.pCore p L := by
    refine eq_pCore_of_normal_of_isSimpleGroup φ.normal_ker
      (fun l hl => φ.mem_ker.mpr (MulEquiv.ext (hO l hl))) fun h => ?_
    obtain ⟨l, v, hlv⟩ := hφ
    have hl : φ l = 1 := φ.mem_ker.mp (h ▸ mem_top l)
    rw [hl] at hlv
    exact hlv rfl
  refine ⟨hker, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ), fun l => ?_⟩
  rfl

theorem simple_core_quotient_centralizer_eq_pCore {G : Type*} [Group G] {p : ℕ}
    {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G)) [IsSimpleGroup (L ⧸ CFSG.pCore p L)]
    (hO : CFSG.inSubgroup (CFSG.pCore p) L ≤ L ⊓ centralizer (V : Set G))
    (hlt : L ⊓ centralizer (V : Set G) < L) :
    L ⊓ centralizer (V : Set G) = CFSG.inSubgroup (CFSG.pCore p) L := by
  set N := (centralizer (V : Set G)).subgroupOf L with hN
  have hNn : N.Normal := by
    refine ⟨fun c hc l => ?_⟩
    rw [hN, mem_subgroupOf, mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : (l : G)⁻¹ * v * l ∈ V := by
      have := (mem_normalizer_iff.mp (hLV (L.inv_mem l.2)) v).mp hv
      rwa [inv_inv] at this
    have hc' := hc _ hv'
    simp only [coe_mul, coe_inv]
    calc v * (l * c * (l : G)⁻¹) = l * (((l : G)⁻¹ * v * l) * c) * (l : G)⁻¹ := by group
      _ = l * (c * ((l : G)⁻¹ * v * l)) * (l : G)⁻¹ := by rw [hc']
      _ = l * c * (l : G)⁻¹ * v := by group
  have hON : CFSG.pCore p L ≤ N := fun x hx =>
    (hO (mem_map_of_mem L.subtype hx)).2
  have hNt : N ≠ ⊤ := by
    intro h
    apply hlt.ne
    refine le_antisymm inf_le_left fun l hl => ⟨hl, ?_⟩
    exact (show (⟨l, hl⟩ : L) ∈ N from h ▸ mem_top _)
  have hEq := eq_pCore_of_normal_of_isSimpleGroup hNn hON hNt
  rw [inf_comm, ← subgroupOf_map_subtype, ← hN, hEq]
  rfl

end CFSG.Quasithin.SteinbergBM
