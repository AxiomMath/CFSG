module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthCoord

public section

namespace CFSG.StandardType

namespace EnnolaFork

open Multiplicative NbrFrameOne

variable {p k : ℕ}

private theorem p5_ne_of_toAdd_ne {u v : MulAut (Multiplicative (Fin k → ZMod p))}
    {t : Fin k → ZMod p} {l : Fin k} (h : toAdd (u (ofAdd t)) l ≠ toAdd (v (ofAdd t)) l) :
    u ≠ v := fun heq => h (by rw [heq])

private theorem p5_toAdd_swapAut_apply (i j l : Fin k) (t : Fin k → ZMod p) :
    toAdd (swapAut i j (ofAdd t)) l = t (Equiv.swap i j l) := by
  rw [swapAut_apply, toAdd_ofAdd, Function.comp_apply]

private theorem p5_toAdd_antiSwapAut_apply {i j : Fin k} (hij : i ≠ j) (l : Fin k)
    (t : Fin k → ZMod p) :
    toAdd (antiSwapAut i j (ofAdd t)) l =
      (if l = i then -t j else if l = j then -t i else t l) := by
  rw [antiSwapAut_apply hij, toAdd_ofAdd]

theorem card_fix_antiSwapAut (hp : p.Prime) {i j : Fin k} (hij : i ≠ j) :
    Nat.card {f : Multiplicative (Fin k → ZMod p) // antiSwapAut i j f = f} * p =
      Nat.card (Multiplicative (Fin k → ZMod p)) := by
  have := Fact.mk hp
  let δ : Multiplicative (Fin k → ZMod p) →* Multiplicative (ZMod p) :=
    { toFun := fun f => ofAdd (toAdd f i + toAdd f j)
      map_one' := by simp
      map_mul' := by
        intro f g
        simp only [toAdd_mul, Pi.add_apply]
        rw [← ofAdd_add]
        congr 1
        ring }
  have hδapp : ∀ f : Multiplicative (Fin k → ZMod p),
      δ f = ofAdd (toAdd f i + toAdd f j) := fun _ => rfl
  have hker : Nat.card δ.ker =
      Nat.card {f : Multiplicative (Fin k → ZMod p) // antiSwapAut i j f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro f
    rw [MonoidHom.mem_ker, hδapp, ← ofAdd_zero, ofAdd.injective.eq_iff]
    constructor
    · intro h
      rw [← ofAdd_toAdd f, antiSwapAut_apply hij, ofAdd.injective.eq_iff]
      funext l
      by_cases hl : l = i
      · subst hl
        rw [if_pos rfl]
        exact neg_eq_iff_add_eq_zero.mpr (by rwa [add_comm] at h)
      · by_cases hl2 : l = j
        · subst hl2
          rw [if_neg hl, if_pos rfl]
          exact neg_eq_iff_add_eq_zero.mpr h
        · rw [if_neg hl, if_neg hl2]
    · intro h
      have h' := congrArg (fun x : Multiplicative (Fin k → ZMod p) => toAdd x i) h
      rw [← ofAdd_toAdd f, antiSwapAut_apply hij] at h'
      simp only [toAdd_ofAdd, if_true] at h'
      have h'' : toAdd f j + toAdd f i = 0 := neg_eq_iff_add_eq_zero.mp h'
      rwa [add_comm] at h''
  have hrange : δ.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨ofAdd (Pi.single i (toAdd x) : Fin k → ZMod p), ?_⟩
    show ofAdd (toAdd (ofAdd (Pi.single i (toAdd x) : Fin k → ZMod p)) i +
      toAdd (ofAdd (Pi.single i (toAdd x) : Fin k → ZMod p)) j) = x
    rw [toAdd_ofAdd, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), add_zero]
    simp
  have hcard_range : Nat.card δ.range = p := by
    rw [hrange]
    calc Nat.card (⊤ : Subgroup (Multiplicative (ZMod p)))
        = Nat.card (Multiplicative (ZMod p)) :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = Nat.card (ZMod p) := Nat.card_congr (Multiplicative.toAdd (α := ZMod p))
      _ = p := Nat.card_zmod p
  have h := TableB.card_range_mul_card_ker δ
  rw [hker, hcard_range, mul_comm] at h
  exact h

theorem forkAut_injective (hp : p.Prime) (hp2 : p ≠ 2) {a b c d : Fin k} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective
      (forkAut a b c d : Fin 4 → MulAut (Multiplicative (Fin k → ZMod p))) := by
  have := Fact.mk hp
  have h01 : (forkAut a b c d 0 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
      forkAut a b c d 1 := by
    rw [forkAut_zero, forkAut_one]
    refine p5_ne_of_toAdd_ne (t := Pi.single a 1) (l := a) ?_
    rw [p5_toAdd_swapAut_apply, p5_toAdd_swapAut_apply,
      Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left,
      Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab)]
    exact one_ne_zero
  have h02 : (forkAut a b c d 0 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
      forkAut a b c d 2 := by
    rw [forkAut_zero, forkAut_two]
    refine p5_ne_of_toAdd_ne (t := Pi.single b 1) (l := b) ?_
    rw [p5_toAdd_swapAut_apply, p5_toAdd_swapAut_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbc hbd,
      Pi.single_eq_of_ne (Ne.symm hbc), Pi.single_eq_same]
    exact zero_ne_one
  have h03 : (forkAut a b c d 0 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
      forkAut a b c d 3 := by
    rw [forkAut_zero, forkAut_three]
    refine p5_ne_of_toAdd_ne (t := Pi.single b 1) (l := b) ?_
    rw [p5_toAdd_swapAut_apply, p5_toAdd_antiSwapAut_apply hcd,
      Equiv.swap_apply_left, if_neg hbc, if_neg hbd,
      Pi.single_eq_of_ne (Ne.symm hbc), Pi.single_eq_same]
    exact zero_ne_one
  have h12 : (forkAut a b c d 1 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
      forkAut a b c d 2 := by
    rw [forkAut_one, forkAut_two]
    refine p5_ne_of_toAdd_ne (t := Pi.single a 1) (l := a) ?_
    rw [p5_toAdd_swapAut_apply, p5_toAdd_swapAut_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac had,
      Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same]
    exact zero_ne_one
  have h13 : (forkAut a b c d 1 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
      forkAut a b c d 3 := by
    rw [forkAut_one, forkAut_three]
    refine p5_ne_of_toAdd_ne (t := Pi.single a 1) (l := a) ?_
    rw [p5_toAdd_swapAut_apply, p5_toAdd_antiSwapAut_apply hcd,
      Equiv.swap_apply_left, if_neg hac, if_neg had,
      Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same]
    exact zero_ne_one
  have h23 : (forkAut a b c d 2 : MulAut (Multiplicative (Fin k → ZMod p))) ≠
      forkAut a b c d 3 := by
    rw [forkAut_two, forkAut_three]
    refine p5_ne_of_toAdd_ne (t := Pi.single c 1) (l := d) ?_
    rw [p5_toAdd_swapAut_apply, p5_toAdd_antiSwapAut_apply hcd,
      Equiv.swap_apply_right, if_neg (Ne.symm hcd), if_pos rfl, Pi.single_eq_same]
    intro h
    exact SpCoord.coord_two_ne_zero hp hp2 (by linear_combination h)
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    simp_all [forkAut_zero, forkAut_one, forkAut_two, forkAut_three]

theorem orderOf_mul_eq_three_of_braid {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hne : x ≠ y) (hb : x * y * x = y * x * y) : orderOf (x * y) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hx
  have hy2 : y * y = 1 := by rw [← pow_two]; exact hy
  have hne1 : x * y ≠ 1 := by
    intro h
    refine hne ?_
    calc x = x * 1 := (mul_one x).symm
      _ = x * (y * y) := by rw [hy2]
      _ = (x * y) * y := by group
      _ = 1 * y := by rw [h]
      _ = y := one_mul y
  refine orderOf_eq_prime ?_ hne1
  calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
        rw [pow_succ, pow_succ, pow_one]; group
    _ = (y * x * y) * (y * x * y) := by rw [← hb]
    _ = y * x * (y * y) * x * y := by group
    _ = y * x * x * y := by rw [hy2]; group
    _ = y * y := by rw [mul_assoc y x x, hx2]; group
    _ = 1 := hy2

theorem orderOf_mul_eq_two_of_commute {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hne : x ≠ y) (hc : x * y = y * x) : orderOf (x * y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hx
  have hy2 : y * y = 1 := by rw [← pow_two]; exact hy
  have hne1 : x * y ≠ 1 := by
    intro h
    refine hne ?_
    calc x = x * 1 := (mul_one x).symm
      _ = x * (y * y) := by rw [hy2]
      _ = (x * y) * y := by group
      _ = 1 * y := by rw [h]
      _ = y := one_mul y
  refine orderOf_eq_prime ?_ hne1
  calc (x * y) ^ 2 = (x * y) * (x * y) := by rw [pow_two]
    _ = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hc]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx2, hy2, mul_one]

end EnnolaFork

end CFSG.StandardType

end
