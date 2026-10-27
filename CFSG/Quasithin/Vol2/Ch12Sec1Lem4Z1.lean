module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4MS
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace Sec1214

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T L V V₁ V₂ T₀ : Subgroup G} {v : G} (c : Setting T L V V₁ V₂ v T₀)
include c

theorem V₁_le_pCoreOf :
    V₁ ≤ pCoreOf 2 (Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) :=
  le_pCoreOf_of_le_normalizer 2 (c.S.V₁_le_lv.trans le_sup_left)
    (sup_le ((Sec1216Lv.lv_le_L L v).trans c.S.ctx.hyp.norm₁) inf_le_right)
    (fun x => ⟨1, Subtype.ext (by simpa using c.S.ctx.hVe.2 x (c.S.ctx.V₁_le x.2))⟩)

theorem v_mem_c134Q : v ∈ c134Q (Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)))
    (Sec1216Lv.lv L v) :=
  Subgroup.commutator_mono c.V₁_le_pCoreOf le_rfl (c.S.V₁_le_commutator c.S.ctx.v_mem_V₁)

omit [Finite G] c in
theorem lv_fix_v : ∀ a ∈ Sec1216Lv.lv L v, a * v * a⁻¹ = v := fun a ha => by
  rw [Subgroup.mem_centralizer_singleton_iff.mp (Sec1216Lv.lv_le_centralizer L v ha),
    mul_inv_cancel_right]

theorem not_case5 : ¬ IsC134Case5 (Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)))
    (T ⊓ Subgroup.normalizer (V₁ : Set G)) (Sec1216Lv.lv L v) := by
  intro hi
  have := c.S.ctx.hVe.1
  obtain ⟨-, h5⟩ := hi
  obtain ⟨hΩ, -⟩ := h5 _ c.isSylowTwoOf_G₀ le_rfl
  obtain ⟨t, ht, htV⟩ := Sec121Swap.exists_mem_not_normalizer c.S.ctx.hyp c.S.ctx.hTL
  obtain ⟨hwU, hw1, hwT⟩ := c.conj_v_mem ht htV
  have hwV : t * v * t⁻¹ ∈ V := c.S.ctx.V₂_le hwU.1
  have hwZ : t * v * t⁻¹ ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) := by
    refine Subgroup.subset_closure ⟨⟨c.S.ctx.V_le_T₁ hwV, Subgroup.mem_centralizer_iff.mpr
      fun s hs => ?_⟩, c.S.ctx.hVe.2 _ hwV⟩
    have h1 := hwT s hs
    calc s * (t * v * t⁻¹) = s * (t * v * t⁻¹) * s⁻¹ * s := by group
      _ = t * v * t⁻¹ * s := by rw [h1]
  have hwc := (hΩ hwZ).2
  exact hw1 (c.S.eq_one_of_fixed hwU fun l hl => by
    rw [Subgroup.mem_centralizer_iff.mp hwc l (Subgroup.mem_sup_left hl), mul_inv_cancel_right])

end Setting

end Sec1214

end CFSG.Quasithin.H13
