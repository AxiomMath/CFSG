module

public import CFSG.Sporadic.Schreier.PairMcLCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def mclWPat : List Bool :=
  [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false,
    true, true]

@[expose] def mclWConds : List (List Bool × ℕ) :=
  [([false, true], 11), ([false, true, false, true, true, true, true], 5),
    ([false, true, true], 12), (mclWPat, 7)]

@[expose] def McLWordConds {G : Type*} [Group G] (x y : G) : Prop :=
  orderOf y = 5 ∧ orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 5 ∧
    orderOf (x * y ^ 2) = 12 ∧
    orderOf (x * y * x * y * x * y * x * y ^ 2 * x * y * x * y ^ 2 * x * y ^ 2) = 7

theorem mclWordConds_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (x y : G) : McLWordConds (f x) (f y) ↔ McLWordConds x y := by
  simp only [McLWordConds, ← map_mul, ← map_inv, ← map_pow, orderOf_injective f hf]

theorem mclWPat_prod {G : Type*} [Group G] (x y : G) :
    (mclWPat.map fun b => if b then y else x).prod =
      x * y * x * y * x * y * x * y ^ 2 * x * y * x * y ^ 2 * x * y ^ 2 := by
  simp [mclWPat, pow_two, mul_assoc]

theorem mclWordConds_iff {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) :
    (orderOf y = 5 ∧ ∀ c ∈ mclWConds, orderOf (c.1.map fun b => if b then y else x).prod = c.2) ↔
      McLWordConds x y := by
  have hxi : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  simp only [McLWordConds, mclWConds, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, mclWPat_prod, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro ⟨hy, h1, h2, h3, h4⟩
    have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyi : y⁻¹ = y * y * y * y := by
      rw [inv_eq_iff_mul_eq_one, ← hy5]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    refine ⟨hy, h1, ?_, by rwa [pow_two], h4⟩
    rw [hxi, hyi]
    simpa only [mul_assoc] using h2
  · rintro ⟨hy, h1, h2, h3, h4⟩
    have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyi : y⁻¹ = y * y * y * y := by
      rw [inv_eq_iff_mul_eq_one, ← hy5]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    refine ⟨hy, h1, ?_, by rwa [pow_two] at h3, h4⟩
    rw [hxi, hyi] at h2
    simpa only [mul_assoc] using h2

@[expose] def mclB0 : Array (Array ℕ) := blockOf 275 [levelArr PairMcL.levels 0]

@[expose] def mclBs : List (Array (Array ℕ)) :=
  [blockOf 275 [levelArr PairMcL.levels 1], blockOf 275 ([2, 3, 4].map (levelArr PairMcL.levels))]

theorem mcl_blocks_eq : PairMcL.blocks = mclB0 :: mclBs := rfl

end CFSG.Sporadic.SmallOddCore
