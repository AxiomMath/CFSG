module

public import CFSG.Quasithin.Vol2.Ch11SecA15Z1c
public import CFSG.Quasithin.Vol2.Ch11SecA15Fix

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem exists_blockU_of_block (hF : Facts15c) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) (hB : IsSL3Block L ∨ IsSp4Block L) {z : G}
    (hz : z ∈ centerOf (ROf T L V₁)) :
    ∃ u₀ ∈ blockU L, u₀⁻¹ * z ∈ Subgroup.centralizer (L : Set G) := by
  rcases hB with hB | hB
  · exact exists_blockU_of_sl3Block hG2 h1102 h hB hz
  · obtain ⟨u, hu, hc⟩ := exists_V1_of_sp4Block hF hG2 h1102 h hU hB hz
    exact ⟨u, fsuV_le_blockU h1102 h (IsVi.le_fsuV hU hu), hc⟩

omit [Finite G] in
theorem IsSL3Block_or_IsSp4Block.isShort2 (hB : IsSL3Block L ∨ IsSp4Block L) : IsShort2 L := by
  rcases hB with hB | hB
  · exact hB.1
  · exact hB.1

theorem V1_eq_omegaOneCenterOf (hF : Facts15) (hFc : Facts15c) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hB : IsSL3Block L ∨ IsSp4Block L) (hC : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    V₁ = omegaOneCenterOf (ROf T L V₁) := by
  have hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    le_bot_iff.mp (hC ▸ inf_le_inf_right _ (fsuV_le_T h))
  have hUL := blockU_eq_of h1102 h (IsSL3Block_or_IsSp4Block.isShort2 hB) hC
  have hZ : centerOf (ROf T L V₁) ≤ V₁ := by
    intro z hz
    obtain ⟨u₀, hu₀, hc⟩ := exists_blockU_of_block hFc hG2 h1102 h hU hB hz
    rw [hUL] at hu₀
    have h1 : u₀⁻¹ * z ∈ T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨T.mul_mem (T.inv_mem (fsuV_le_T h hu₀)) (ROf_le_T h hz.1), hc⟩
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    exact mem_V1_of_fixed hF h1102 h hU hu₀ fun r hr => by
      rw [Subgroup.mem_centralizer_iff.mp hz.2 r hr, mul_inv_cancel_right]
  apply le_antisymm
  · intro u hu
    have huV := IsVi.le_fsuV hU hu
    refine Subgroup.subset_closure ⟨⟨fsuV_le_ROf h huV, Subgroup.mem_centralizer_iff.mpr
      fun r hr => ?_⟩, (isElemAbelian_fsuV h).2 u huV⟩
    exact (Subgroup.mem_centralizer_iff.mp (ROf_le_centralizer_V1 hF h1102 h hU hCV hr) u hu).symm
  · exact (Subgroup.closure_le _).mpr fun x hx => hZ hx.1

end CFSG.Quasithin.Vol2.Ch11.SecA
