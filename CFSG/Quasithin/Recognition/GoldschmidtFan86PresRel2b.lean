module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresRel2a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres2
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.Fan86

namespace PresP2

local macro "lsimp" : tactic =>
  `(tactic| simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, gen_xb, gen_t, gen_w1,
    gen_w2, gen_ub, gen_zm, gen_ym, gen_za, fcomm, XB, T, W1, W2, UB, ZM, YM, ZA])

variable {H : Type*} [Group H] {xb t w1 w2 ub : H} {zm ym za : Fin 3 → H}

theorem lift_rels912 (h : P2Rel912 xb t w1 w2 ub zm ym za) :
    ∀ r ∈ rels912, FreeGroup.lift (gen xb t w1 w2 ub zm ym za) r = 1 := by
  simp only [rels912, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_flatMap,
    List.mem_finRange, true_implies, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun i => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    fun i j => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · lsimp; exact h.x3
  · lsimp; exact h.t2
  · lsimp; exact mul_eq_one_iff_eq_inv.2 h.xt
  · lsimp; exact mul_inv_eq_one.2 h.w1sq
  · lsimp; exact h.ub2
  · lsimp; exact mul_inv_eq_one.2 h.xub
  · lsimp; exact mul_inv_eq_one.2 h.tub
  · lsimp; exact mul_inv_eq_one.2 h.w1z1
  · lsimp; exact mul_inv_eq_one.2 h.w1z2
  · lsimp; exact h.w1z3
  · lsimp; exact mul_inv_eq_one.2 h.w1y1
  · lsimp; exact mul_inv_eq_one.2 h.w1y2
  · lsimp; exact mul_inv_eq_one.2 h.w1ub
  · lsimp; exact h.yub
  · lsimp; exact h.prod_y
  · lsimp; exact h.prod_za
  · lsimp; exact h.zm2 i
  · lsimp; exact h.ym2 i
  · lsimp; exact h.za2 i
  · lsimp; exact mul_inv_eq_one.2 (h.xz i)
  · lsimp; exact mul_inv_eq_one.2 (h.xy i)
  · lsimp; exact mul_inv_eq_one.2 (h.xa i)
  · lsimp; exact mul_inv_eq_one.2 (h.tz i)
  · lsimp; exact mul_inv_eq_one.2 (h.ty i)
  · lsimp; exact mul_inv_eq_one.2 (h.ta i)
  · lsimp; exact h.zyi i
  · lsimp; exact h.zub i
  · lsimp; exact h.yza i
  · lsimp; exact h.uza i
  · lsimp; exact h.zaw1 i
  · lsimp; exact h.zaw2 i
  · lsimp; exact h.zaz i j
  · lsimp; exact h.zay i j
  · lsimp; exact h.zaza i j
  · intro r hr
    by_cases hij : i = j
    · simp [hij] at hr
    · simp only [hij, ite_false, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · lsimp; exact mul_inv_eq_one.2 (h.zz i j hij)
      · lsimp; exact mul_inv_eq_one.2 (h.zy i j hij)

end PresP2

end CFSG.Quasithin.Fan86
