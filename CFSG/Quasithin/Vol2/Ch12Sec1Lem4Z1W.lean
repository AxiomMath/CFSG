module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4Z1
public import CFSG.Quasithin.Vol2.Ch12Sec1Case4CountPfW
public import CFSG.Quasithin.EmptyFaithful.A38c10MSb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace Sec1214

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T L V V₁ V₂ T₀ : Subgroup G} {v : G} (c : Setting T L V V₁ V₂ v T₀)
include c

theorem exists_mem_omegaOneCenterOfW (h134 : C134L32CorrM) :
    ∃ z ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)), z ≠ 1 ∧
      z ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨α, hα⟩ := c.exists_isModO2Surj
  obtain ⟨i, hi⟩ := h134 G _ _ _ c.isMSPair c.S.mem_lFamily c.coe_G₀
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi => exact (A38c10.MS.false_of_case_one_two_three (i := 1) hi (Or.inl rfl) c.v_mem_c134Q
      c.S.ctx.v_ne_one lv_fix_v).elim
  | 2, hi => exact (A38c10.MS.false_of_case_one_two_three (i := 2) hi (Or.inr (Or.inl rfl))
      c.v_mem_c134Q c.S.ctx.v_ne_one lv_fix_v).elim
  | 3, hi => exact (A38c10.MS.false_of_case_one_two_three (i := 3) hi (Or.inr (Or.inr rfl))
      c.v_mem_c134Q c.S.ctx.v_ne_one lv_fix_v).elim
  | 4, hi => exact (Sec1214.notCase4Min_holds _ _ _ _ _ _ _ _ c hi).elim
  | 5, hi => exact (c.not_case5 hi).elim
  | n + 6, hi => exact hi.elim

end Setting

end Sec1214

end CFSG.Quasithin.H13
