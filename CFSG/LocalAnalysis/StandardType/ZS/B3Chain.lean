module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

theorem b3Chain_apply {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    let g := permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
      permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
      diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)
    g (f (i0.succAbove 0)) = f (i0.succAbove 1) ∧
      g (f (i0.succAbove 1)) = f (i0.succAbove 2) ∧
      g (f (i0.succAbove 2)) = - f (i0.succAbove 0) ∧ g (f i0) = f i0 := by
  dsimp only
  have h01 : i0.succAbove 0 ≠ i0.succAbove 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (Fin.succAbove_right_injective h)
  have h02 : i0.succAbove 0 ≠ i0.succAbove 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (Fin.succAbove_right_injective h)
  have h12 : i0.succAbove 1 ≠ i0.succAbove 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (Fin.succAbove_right_injective h)
  have h0 : i0.succAbove 0 ≠ i0 := Fin.succAbove_ne i0 0
  have h1 : i0.succAbove 1 ≠ i0 := Fin.succAbove_ne i0 1
  have h2 : i0.succAbove 2 ≠ i0 := Fin.succAbove_ne i0 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagMap_apply_basis,
      if_neg h02, Units.val_one, one_smul, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne h01 h02, permMap_apply_basis, Equiv.swap_apply_left]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagMap_apply_basis,
      if_neg h12, Units.val_one, one_smul, permMap_apply_basis, Equiv.swap_apply_left,
      permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12)]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagMap_apply_basis, if_pos rfl,
      Units.val_neg, Units.val_one, neg_one_smul, map_neg, permMap_apply_basis,
      Equiv.swap_apply_right, map_neg, permMap_apply_basis, Equiv.swap_apply_right]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagMap_apply_basis,
      if_neg (Ne.symm h2), Units.val_one, one_smul, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2), permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h0) (Ne.symm h1)]

private theorem b3Chain_index_ne (i0 : Fin 4) :
    i0.succAbove 0 ≠ i0.succAbove 1 ∧ i0.succAbove 0 ≠ i0.succAbove 2 ∧
      i0.succAbove 1 ≠ i0.succAbove 2 ∧ i0.succAbove 0 ≠ i0 ∧
      i0.succAbove 1 ≠ i0 ∧ i0.succAbove 2 ≠ i0 := by
  refine ⟨?_, ?_, ?_, Fin.succAbove_ne i0 0, Fin.succAbove_ne i0 1, Fin.succAbove_ne i0 2⟩
  · intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (Fin.succAbove_right_injective h)
  · intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (Fin.succAbove_right_injective h)
  · intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (Fin.succAbove_right_injective h)

private theorem b3Chain_pair12_apply_basis {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    let g := permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
      permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2))
    g (f (i0.succAbove 0)) = f (i0.succAbove 1) ∧
      g (f (i0.succAbove 1)) = f (i0.succAbove 2) ∧
      g (f (i0.succAbove 2)) = f (i0.succAbove 0) ∧ g (f i0) = f i0 := by
  dsimp only
  obtain ⟨h01, h02, h12, h0, h1, h2⟩ := b3Chain_index_ne i0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne h01 h02, permMap_apply_basis, Equiv.swap_apply_left]
  · rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_left,
      permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12)]
  · rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_right,
      permMap_apply_basis, Equiv.swap_apply_right]
  · rw [LinearEquiv.mul_apply, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2), permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h0) (Ne.symm h1)]

private theorem b3Chain_pair23_apply_basis {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    let g := permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
      diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)
    g (f (i0.succAbove 0)) = f (i0.succAbove 0) ∧
      g (f (i0.succAbove 1)) = f (i0.succAbove 2) ∧
      g (f (i0.succAbove 2)) = - f (i0.succAbove 1) ∧ g (f i0) = f i0 := by
  dsimp only
  obtain ⟨h01, h02, h12, -, h1, h2⟩ := b3Chain_index_ne i0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_neg h02, Units.val_one, one_smul,
      permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne h01 h02]
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_neg h12, Units.val_one, one_smul,
      permMap_apply_basis, Equiv.swap_apply_left]
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_pos rfl, Units.val_neg, Units.val_one,
      neg_one_smul, map_neg, permMap_apply_basis, Equiv.swap_apply_right]
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_neg (Ne.symm h2), Units.val_one,
      one_smul, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h2)]

private theorem b3Chain_pair13_apply_basis {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    let g := permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
      diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)
    g (f (i0.succAbove 0)) = f (i0.succAbove 1) ∧
      g (f (i0.succAbove 1)) = f (i0.succAbove 0) ∧
      g (f (i0.succAbove 2)) = - f (i0.succAbove 2) ∧ g (f i0) = f i0 := by
  dsimp only
  obtain ⟨h01, h02, h12, h0, h1, h2⟩ := b3Chain_index_ne i0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_neg h02, Units.val_one, one_smul,
      permMap_apply_basis, Equiv.swap_apply_left]
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_neg h12, Units.val_one, one_smul,
      permMap_apply_basis, Equiv.swap_apply_right]
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_pos rfl, Units.val_neg, Units.val_one,
      neg_one_smul, map_neg, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12)]
  · rw [LinearEquiv.mul_apply, diagMap_apply_basis, if_neg (Ne.symm h2), Units.val_one,
      one_smul, permMap_apply_basis,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h0) (Ne.symm h1)]

private theorem orderOf_b3Chain_pair12_basis {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    orderOf (permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
      permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2))) = 3 := by
  obtain ⟨ha, hb, hc, hi⟩ := b3Chain_pair12_apply_basis f i0
  obtain ⟨h01, -, -, -, -, -⟩ := b3Chain_index_ne i0
  set g := permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
    permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2))
  clear_value g
  have hpow : g ^ 3 = 1 := by
    refine f.ext' fun k => ?_
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change g (g (g (f k))) = f k
    rcases Fin.eq_self_or_eq_succAbove i0 k with rfl | ⟨j, rfl⟩
    · rw [hi, hi, hi]
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
      · rw [ha, hb, hc]
      · rw [hb, hc, ha]
      · rw [hc, ha, hb]
  have hne : g ≠ 1 := by
    intro h
    have h1 : g (f (i0.succAbove 0)) = f (i0.succAbove 0) := by rw [h]; simp
    rw [ha] at h1
    exact h01 (f.injective h1).symm
  exact orderOf_eq_prime (p := 3) (hp := ⟨Nat.prime_three⟩) hpow hne

private theorem orderOf_b3Chain_pair23_basis (hp2 : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    orderOf (permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
      diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)) = 4 := by
  obtain ⟨ha, hb, hc, hi⟩ := b3Chain_pair23_apply_basis f i0
  set g := permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
    diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)
  clear_value g
  have h2a : (g ^ 2) (f (i0.succAbove 0)) = f (i0.succAbove 0) := by
    rw [pow_two, LinearEquiv.mul_apply, ha, ha]
  have h2i : (g ^ 2) (f i0) = f i0 := by
    rw [pow_two, LinearEquiv.mul_apply, hi, hi]
  have h2b : (g ^ 2) (f (i0.succAbove 1)) = - f (i0.succAbove 1) := by
    rw [pow_two, LinearEquiv.mul_apply, hb, hc]
  have h2c : (g ^ 2) (f (i0.succAbove 2)) = - f (i0.succAbove 2) := by
    rw [pow_two, LinearEquiv.mul_apply, hc, map_neg, hb]
  have hpow : g ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
    refine f.ext' fun k => ?_
    rw [LinearEquiv.mul_apply]
    change (g ^ 2) ((g ^ 2) (f k)) = f k
    rcases Fin.eq_self_or_eq_succAbove i0 k with rfl | ⟨j, rfl⟩
    · rw [h2i, h2i]
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
      · rw [h2a, h2a]
      · rw [h2b, map_neg, h2b, neg_neg]
      · rw [h2c, map_neg, h2c, neg_neg]
  have hne : g ^ 2 ≠ 1 := by
    intro h
    have h1 : (g ^ 2) (f (i0.succAbove 1)) = f (i0.succAbove 1) := by
      rw [h]; simp
    rw [h2b] at h1
    have hsum : f (i0.succAbove 1) + f (i0.succAbove 1) = 0 :=
      (neg_eq_iff_add_eq_zero).mp h1
    have h2 : (2 : ZMod p) • f (i0.succAbove 1) = 0 := by simpa [two_smul] using hsum
    have hzero : f (i0.succAbove 1) = 0 :=
      (smul_eq_zero_iff_right ((CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) Nat.prime_two hp2))).mp h2
    exact f.ne_zero (i0.succAbove 1) hzero
  have hnot : ¬ g ^ 2 ^ 1 = 1 := by simpa using hne
  have hfin : g ^ 2 ^ (1 + 1) = 1 := by simpa using hpow
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (hp := ⟨Nat.prime_two⟩) hnot hfin

private theorem orderOf_b3Chain_pair13_basis {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    orderOf (permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
      diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)) = 2 := by
  obtain ⟨ha, hb, hc, hi⟩ := b3Chain_pair13_apply_basis f i0
  obtain ⟨h01, -, -, -, -, -⟩ := b3Chain_index_ne i0
  set g := permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
    diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)
  clear_value g
  have hpow : g ^ 2 = 1 := by
    refine f.ext' fun k => ?_
    rw [pow_two, LinearEquiv.mul_apply]
    change g (g (f k)) = f k
    rcases Fin.eq_self_or_eq_succAbove i0 k with rfl | ⟨j, rfl⟩
    · rw [hi, hi]
    · obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
      · rw [ha, hb]
      · rw [hb, ha]
      · rw [hc, map_neg, hc, neg_neg]
  have hne : g ≠ 1 := by
    intro h
    have h1 : g (f (i0.succAbove 0)) = f (i0.succAbove 0) := by rw [h]; simp
    rw [ha] at h1
    exact h01 (f.injective h1).symm
  exact orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) hpow hne

theorem orderOf_b3Chain {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (hp2 : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    orderOf (permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
        permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2))) = 3 ∧
      orderOf (permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
        diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)) = 4 ∧
      orderOf (permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
        diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)) = 2 := by
  exact ⟨orderOf_b3Chain_pair12_basis f i0,
    orderOf_b3Chain_pair23_basis hp2 f i0,
    orderOf_b3Chain_pair13_basis f i0⟩

theorem b3Chain_cube {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4) :
    (permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
        permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
        diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)) ^ 3 =
      diagMap p f (fun j => if j = i0 then 1 else -1) := by
  obtain ⟨ha, hb, hc, hi⟩ := b3Chain_apply f i0
  set g := permMap p f (Equiv.swap (i0.succAbove 0) (i0.succAbove 1)) *
    permMap p f (Equiv.swap (i0.succAbove 1) (i0.succAbove 2)) *
    diagMap p f (fun j => if j = i0.succAbove 2 then -1 else 1)
  clear_value g
  refine f.ext' fun k => ?_
  rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagMap_apply_basis]
  rcases Fin.eq_self_or_eq_succAbove i0 k with rfl | ⟨j, rfl⟩
  · rw [hi, hi, hi, if_pos rfl, Units.val_one, one_smul]
  · rw [if_neg (Fin.succAbove_ne i0 j), Units.val_neg, Units.val_one, neg_one_smul]
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> decide
    · rw [ha, hb, hc]
    · rw [hb, hc, map_neg, ha]
    · rw [hc, map_neg, ha, map_neg, hb]

private theorem diagMap_equivFun {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ) (v : U) :
    f.equivFun (diagMap p f d v) = fun i => (d i : ZMod p) * f.equivFun v i := by
  rw [diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  funext i
  rw [LinearEquiv.piCongrRight_apply]
  rfl

private theorem diagMap_sign_equivFun {n : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin n) (ZMod p) U) (i0 : Fin n) (v : U) :
    f.equivFun (diagMap p f (fun j => if j = i0 then 1 else -1) v) =
      fun i => (if i = i0 then (1 : ZMod p) else -1) * f.equivFun v i := by
  rw [diagMap_equivFun]
  funext i
  by_cases hi : i = i0 <;> simp [hi]

private theorem eq_smul_basis_of_fix_diagMap_sign {n : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (hp2 : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U) (i0 : Fin n)
    {v : U} (hv : diagMap p f (fun j => if j = i0 then 1 else -1) v = v) :
    v = f.equivFun v i0 • f i0 := by
  refine f.ext_elem fun k => ?_
  change f.equivFun v k = f.equivFun (f.equivFun v i0 • f i0) k
  by_cases hk : k = i0
  · subst hk
    simp
  · have hik : i0 ≠ k := Ne.symm hk
    have hcoord := congrFun (diagMap_sign_equivFun f i0 v) k
    rw [hv] at hcoord
    have hcoord' : (if k = i0 then (1 : ZMod p) else -1) * f.equivFun v k =
        f.equivFun v k := hcoord.symm
    rw [if_neg hk, neg_one_mul] at hcoord'
    have h2 : (2 : ZMod p) * f.equivFun v k = 0 := by
      have hsum : f.equivFun v k + f.equivFun v k = 0 := (neg_eq_iff_add_eq_zero).mp hcoord'
      simpa [two_mul] using hsum
    have hzero : f.equivFun v k = 0 :=
      (mul_eq_zero.mp h2).resolve_left ((CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) Nat.prime_two hp2))
    simp [hik, hzero]

private theorem span_range_eq_of_diagMap_sign_fix {n : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (hp2 : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U) (i0 : Fin n)
    {s : U ≃ₗ[ZMod p] U} (hs : IsRefl p s) {w : U}
    (hw : w = s (f i0) - f i0) (hwne : w ≠ 0)
    (hzw : diagMap p f (fun j => if j = i0 then 1 else -1) w = w) :
    LinearMap.range ((s : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ f i0 := by
  have hw_eq : w = f.equivFun w i0 • f i0 :=
    eq_smul_basis_of_fix_diagMap_sign hp2 f i0 hzw
  have hc0 : f.equivFun w i0 ≠ 0 := by
    intro h
    exact hwne (by rw [hw_eq, h, zero_smul])
  have hwmem : w ∈ LinearMap.range ((s : U →ₗ[ZMod p] U) - LinearMap.id) := by
    refine ⟨f i0, ?_⟩
    show s (f i0) - f i0 = w
    rw [hw]
  have hspanw : LinearMap.range ((s : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one hs.2 hwmem hwne
  rw [hspanw, hw_eq, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0)]

private theorem eq_of_mem_span_of_commute_diagMap_sign {n : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (hp2 : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U) (i0 : Fin n)
    {s : U ≃ₗ[ZMod p] U}
    (hc : Commute s (diagMap p f (fun j => if j = i0 then 1 else -1)))
    (hspan : LinearMap.range ((s : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ f i0)
    {k : Fin n} (hk : k ≠ i0) : s (f k) = f k := by
  set z : U ≃ₗ[ZMod p] U := diagMap p f (fun j => if j = i0 then 1 else -1)
  have hzi : z (f i0) = f i0 := by
    change diagMap p f (fun j => if j = i0 then 1 else -1) (f i0) = f i0
    rw [diagMap_apply_basis]
    simp
  have hzk : z (f k) = - f k := by
    change diagMap p f (fun j => if j = i0 then 1 else -1) (f k) = - f k
    rw [diagMap_apply_basis, if_neg hk]
    simp
  have hzs : z (s (f k)) = s (z (f k)) := by
    have h := congrArg (fun g : U ≃ₗ[ZMod p] U => g (f k)) hc.symm
    simpa only [LinearEquiv.mul_apply] using h
  have hmem : s (f k) - f k ∈ ZMod p ∙ f i0 := by
    rw [← hspan]
    exact ⟨f k, rfl⟩
  obtain ⟨d, hdu⟩ := Submodule.mem_span_singleton.mp hmem
  have hzu : z (s (f k) - f k) = -(s (f k) - f k) := by
    rw [map_sub, hzs, hzk, map_neg]
    abel
  have h1 : z (s (f k) - f k) = s (f k) - f k := by
    rw [← hdu, map_smul, hzi]
  have hsum : (s (f k) - f k) + (s (f k) - f k) = 0 :=
    (eq_neg_iff_add_eq_zero).mp (h1.symm.trans hzu)
  have h2 : (2 : ZMod p) • (s (f k) - f k) = 0 := by simpa [two_smul] using hsum
  have hzero : s (f k) - f k = 0 :=
    (smul_eq_zero_iff_right ((CharP.cast_ne_zero_of_ne_of_prime (R := ZMod p) Nat.prime_two hp2))).mp h2
  exact sub_eq_zero.mp hzero

private theorem fix_off_i0_of_commute_diagMap_sign {n : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (hp2 : p ≠ 2) (f : Module.Basis (Fin n) (ZMod p) U) (i0 : Fin n)
    {s : U ≃ₗ[ZMod p] U} (hs : IsRefl p s)
    (hc : Commute s (diagMap p f (fun j => if j = i0 then 1 else -1)))
    (hwne : s (f i0) - f i0 ≠ 0) :
    LinearMap.range ((s : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ f i0 ∧
      ∀ k, k ≠ i0 → s (f k) = f k := by
  set z : U ≃ₗ[ZMod p] U := diagMap p f (fun j => if j = i0 then 1 else -1)
  have hzi : z (f i0) = f i0 := by
    change diagMap p f (fun j => if j = i0 then 1 else -1) (f i0) = f i0
    rw [diagMap_apply_basis]
    simp
  have hzs : ∀ v, z (s v) = s (z v) := by
    intro v
    have h := congrArg (fun g : U ≃ₗ[ZMod p] U => g v) hc.symm
    simpa only [LinearEquiv.mul_apply] using h
  set w : U := s (f i0) - f i0 with hw
  have hwne' : w ≠ 0 := by rw [hw]; exact hwne
  have hzw : z w = w := by
    rw [hw, map_sub, hzs, hzi]
  have hspan : LinearMap.range ((s : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ f i0 :=
    span_range_eq_of_diagMap_sign_fix hp2 f i0 hs hw hwne' hzw
  exact ⟨hspan, fun k hk =>
    eq_of_mem_span_of_commute_diagMap_sign hp2 f i0 hc hspan hk⟩

private theorem eq_diagMap_sign_of_apply {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4)
    {s : U ≃ₗ[ZMod p] U} (hi : s (f i0) = - f i0)
    (hk : ∀ k, k ≠ i0 → s (f k) = f k) :
    s = diagMap p f (fun j => if j = i0 then -1 else 1) := by
  refine f.ext' fun k => ?_
  rcases Fin.eq_self_or_eq_succAbove i0 k with rfl | ⟨j, rfl⟩
  · rw [hi, diagMap_apply_basis]
    simp
  · rw [hk _ (Fin.succAbove_ne i0 j), diagMap_apply_basis,
      if_neg (Fin.succAbove_ne i0 j)]
    simp

private theorem eq_sgn_of_commute_diagMap_sign_of_ne_zero {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (hp2 : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4)
    {s : U ≃ₗ[ZMod p] U} (hs : IsRefl p s)
    (hc : Commute s (diagMap p f (fun j => if j = i0 then 1 else -1)))
    (hwne : s (f i0) - f i0 ≠ 0) :
    s = diagMap p f (fun j => if j = i0 then -1 else 1) := by
  obtain ⟨hspan, hfixk⟩ := fix_off_i0_of_commute_diagMap_sign hp2 f i0 hs hc hwne
  have hmem : s (f i0) - f i0 ∈ ZMod p ∙ f i0 := by
    rw [← hspan]
    exact ⟨f i0, rfl⟩
  obtain ⟨c, hc_eq⟩ := Submodule.mem_span_singleton.mp hmem
  have hsi : s (f i0) = (1 + c) • f i0 := by
    have h1 : s (f i0) = s (f i0) - f i0 + f i0 := by abel
    rw [h1, ← hc_eq, add_smul, one_smul]
    abel
  have hc0 : c ≠ 0 := by
    intro h
    exact hwne (by rw [← hc_eq, h, zero_smul])
  have hsq : (1 + c) * (1 + c) = 1 := by
    have h2 : s (s (f i0)) = f i0 := by
      have h := congrArg (fun g : U ≃ₗ[ZMod p] U => g (f i0)) hs.1
      simpa using h
    rw [hsi, map_smul, hsi, smul_smul] at h2
    have h3 := congrFun (congrArg f.equivFun h2) i0
    simpa using h3
  have hlam : 1 + c = -1 := by
    have hcases : 1 + c = 1 ∨ 1 + c = -1 := by
      rw [← sq_eq_one_iff, pow_two]
      exact hsq
    rcases hcases with h1 | h1
    · exfalso
      have hc0zero : c = 0 := by simpa using h1
      exact hc0 hc0zero
    · exact h1
  refine eq_diagMap_sign_of_apply f i0 ?_ hfixk
  rw [hsi, hlam, neg_one_smul]

theorem fix_or_eq_sgn_of_commute {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (hp2 : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) (i0 : Fin 4)
    {s : U ≃ₗ[ZMod p] U} (hs : IsRefl p s)
    (hc : Commute s (diagMap p f (fun j => if j = i0 then 1 else -1))) :
    s (f i0) = f i0 ∨ s = diagMap p f (fun j => if j = i0 then -1 else 1) := by
  by_cases hw0 : s (f i0) - f i0 = 0
  · exact Or.inl (sub_eq_zero.mp hw0)
  · exact Or.inr (eq_sgn_of_commute_diagMap_sign_of_ne_zero hp2 f i0 hs hc hw0)
