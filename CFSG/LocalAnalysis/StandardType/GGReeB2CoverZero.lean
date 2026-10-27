module

public import CFSG.LocalAnalysis.StandardType.GGReeB2CondCDefs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.ReeB2Fixed

private def E (e : ℕ) (p : Fin e) : ZMod (2 ^ e - 1) :=
  2 ^ (p : ℕ) * R e

private theorem two_pow_e_eq_one (e : ℕ) (he : Odd e) :
    (2 : ZMod (2 ^ e - 1)) ^ e = 1 := by
  have hsub : ((2 ^ e - 1 : ℕ) : ZMod (2 ^ e - 1)) = 0 := ZMod.natCast_self _
  have hsplit : (2 ^ e : ℕ) = (2 ^ e - 1) + 1 := by
    have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hsplit_cast : ((2 ^ e : ℕ) : ZMod (2 ^ e - 1)) =
      ((2 ^ e - 1 : ℕ) : ZMod (2 ^ e - 1)) + 1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod (2 ^ e - 1))) hsplit
    simpa [Nat.cast_add, Nat.cast_one] using h
  calc
    (2 : ZMod (2 ^ e - 1)) ^ e = ((2 ^ e : ℕ) : ZMod (2 ^ e - 1)) :=
      (Nat.cast_pow 2 e).symm
    _ = ((2 ^ e - 1 : ℕ) : ZMod (2 ^ e - 1)) + 1 := hsplit_cast
    _ = 1 := by rw [hsub, zero_add]

private theorem two_pow_succσ (e : ℕ) (he : Odd e) (p : Fin e) :
    (2 : ZMod (2 ^ e - 1)) ^ (succσ e p : ℕ) =
      2 ^ (p : ℕ) * 2 ^ ((e + 1) / 2) := by
  have hval : (succσ e p : ℕ) = ((p : ℕ) + (e + 1) / 2) % e := rfl
  rw [hval, ← pow_eq_pow_mod ((p : ℕ) + (e + 1) / 2) (two_pow_e_eq_one e he)]
  rw [pow_add]

private theorem succσ_injective (e : ℕ) (he : Odd e) [NeZero e] :
    Function.Injective (succσ e) := by
  intro a b hab
  have hmod : ((a : ℕ) + (e + 1) / 2) % e = ((b : ℕ) + (e + 1) / 2) % e := by
    simpa [succσ] using congrArg Fin.val hab
  have hcongr : (a : ℕ) + (e + 1) / 2 ≡ (b : ℕ) + (e + 1) / 2 [MOD e] := hmod
  have hcongr2 : (a : ℕ) ≡ (b : ℕ) [MOD e] :=
    Nat.ModEq.add_right_cancel' ((e + 1) / 2) hcongr
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hcongr2 a.isLt b.isLt)

private theorem succσ_bijective (e : ℕ) (he : Odd e) [NeZero e] :
    Function.Bijective (succσ e) :=
  (succσ_injective e he).bijective_of_finite

private theorem two_pow_h_sq (e : ℕ) (he : Odd e) :
    ((2 : ZMod (2 ^ e - 1)) ^ ((e + 1) / 2)) ^ 2 = 2 := by
  have heodd : Odd e := he
  obtain ⟨k, hk⟩ := he
  have hh : (e + 1) / 2 = k + 1 := by
    rw [hk]
    have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    rw [h2]
    exact Nat.mul_div_cancel_left (k + 1) (by norm_num)
  have hexp : (k + 1) * 2 = e + 1 := by
    rw [hk]
    ring
  rw [hh, ← pow_mul, hexp]
  rw [pow_succ]
  rw [two_pow_e_eq_one e heodd]
  ring

private theorem sum_E_eq_zero (e : ℕ) (he : Odd e) [NeZero e] :
    ∑ p : Fin e, E e p = 0 := by
  have hE : ∀ p : Fin e,
      E e p = (2 : ZMod (2 ^ e - 1)) ^ (succσ e p : ℕ) - 2 ^ (p : ℕ) := by
    intro p
    unfold E R
    rw [two_pow_succσ e he p]
    ring
  calc
    ∑ p : Fin e, E e p
        = ∑ p : Fin e,
            ((2 : ZMod (2 ^ e - 1)) ^ (succσ e p : ℕ) - 2 ^ (p : ℕ)) :=
          Finset.sum_congr rfl (fun p _ => hE p)
    _ = (∑ p : Fin e, (2 : ZMod (2 ^ e - 1)) ^ (succσ e p : ℕ)) -
          ∑ p : Fin e, 2 ^ (p : ℕ) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
          have hbij : Function.Bijective (succσ e) := succσ_bijective e he
          have hcomp : (∑ p : Fin e, (2 : ZMod (2 ^ e - 1)) ^ (succσ e p : ℕ)) =
              ∑ p : Fin e, 2 ^ (p : ℕ) :=
            hbij.sum_comp (fun p : Fin e => (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ))
          rw [hcomp, sub_self]

private theorem E_add_E_succσ (e : ℕ) (he : Odd e) (p : Fin e) :
    E e p + E e (succσ e p) = 2 ^ (p : ℕ) := by
  unfold E R
  rw [two_pow_succσ e he p]
  calc
    (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) * (2 ^ ((e + 1) / 2) - 1) +
        ((2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) * 2 ^ ((e + 1) / 2)) *
          (2 ^ ((e + 1) / 2) - 1)
        = (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) *
            ((2 ^ ((e + 1) / 2) - 1) * (1 + 2 ^ ((e + 1) / 2))) := by
          ring
    _ = (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) * ((2 ^ ((e + 1) / 2)) ^ 2 - 1) := by ring
    _ = (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) * (2 - 1) := by rw [two_pow_h_sq e he]
    _ = (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) := by ring

private def cJ (e : ℕ) (J : Finset (Fin e)) (p : Fin e) : ZMod (2 ^ e - 1) :=
  if succσ e p ∈ J then R e else 1

private theorem cJ_mem_units (e : ℕ) (J : Finset (Fin e)) (p : Fin e) :
    cJ e J p ∈ units e := by
  unfold cJ
  by_cases h : succσ e p ∈ J
  · rw [if_pos h]
    simp [units]
  · rw [if_neg h]
    simp [units]

private theorem sum_cJ_mul_eq_zero (e : ℕ) (he : Odd e) [NeZero e] (J : Finset (Fin e))
    (hJ : ∀ p, p ∈ J ∨ succσ e p ∈ J) :
    ∑ p ∈ J, cJ e J p * 2 ^ (p : ℕ) = 0 := by
  have hJ1 : ∀ p ∈ J.filter (fun p => succσ e p ∈ J),
      cJ e J p * 2 ^ (p : ℕ) = E e p := by
    intro p hp
    have hsp : succσ e p ∈ J := (Finset.mem_filter.mp hp).2
    unfold cJ E R
    rw [if_pos hsp]
    ring
  have hJ2 : ∀ p ∈ J.filter (fun p => succσ e p ∉ J),
      cJ e J p * 2 ^ (p : ℕ) = E e p + E e (succσ e p) := by
    intro p hp
    have hsp : succσ e p ∉ J := (Finset.mem_filter.mp hp).2
    unfold cJ
    rw [if_neg hsp, one_mul, E_add_E_succσ e he p]
  have h1 : ∑ p ∈ J.filter (fun p => succσ e p ∈ J), cJ e J p * 2 ^ (p : ℕ)
      = ∑ p ∈ J.filter (fun p => succσ e p ∈ J), E e p :=
    Finset.sum_congr rfl (fun p hp => hJ1 p hp)
  have h2 : ∑ p ∈ J.filter (fun p => succσ e p ∉ J), cJ e J p * 2 ^ (p : ℕ)
      = ∑ p ∈ J.filter (fun p => succσ e p ∉ J), E e p +
        ∑ p ∈ J.filter (fun p => succσ e p ∉ J), E e (succσ e p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p hp => hJ2 p hp)
  have himage : (J.filter (fun p => succσ e p ∉ J)).image (succσ e) = Jᶜ := by
    ext i
    constructor
    · intro hi
      obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hi
      rw [← hpi]
      exact Finset.mem_compl.mpr (Finset.mem_filter.mp hp).2
    · intro hi
      have hiJ : i ∉ J := Finset.mem_compl.mp hi
      obtain ⟨p, hpσ⟩ := (succσ_bijective e he).2 i
      have hpJ : p ∈ J := by
        rcases hJ p with h | h
        · exact h
        · rw [hpσ] at h
          exact absurd h hiJ
      exact Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hpJ, by rw [hpσ]; exact hiJ⟩, hpσ⟩
  have hJ2sum : ∑ p ∈ J.filter (fun p => succσ e p ∉ J), E e (succσ e p) =
      ∑ i ∈ Jᶜ, E e i := by
    rw [← Finset.sum_image (succσ_injective e he).injOn, himage]
  have hJsum : ∑ p ∈ J.filter (fun p => succσ e p ∈ J), E e p +
      ∑ p ∈ J.filter (fun p => succσ e p ∉ J), E e p = ∑ p ∈ J, E e p := by
    have h := Finset.sum_filter_add_sum_filter_not J (fun p => succσ e p ∈ J)
      (fun p => E e p)
    simpa using h
  have htotal : ∑ p ∈ J.filter (fun p => succσ e p ∈ J), E e p +
      (∑ p ∈ J.filter (fun p => succσ e p ∉ J), E e p + ∑ i ∈ Jᶜ, E e i) = 0 := by
    rw [← add_assoc, hJsum, Finset.sum_add_sum_compl]
    exact sum_E_eq_zero e he
  have hsplit := Finset.sum_filter_add_sum_filter_not J (fun p => succσ e p ∈ J)
    (fun p => cJ e J p * 2 ^ (p : ℕ))
  rw [← hsplit, h1, h2, hJ2sum]
  exact htotal

theorem zero_mem_lam_of_cover (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) (J : Finset (Fin e))
    (hJ : ∀ p, p ∈ J ∨ succσ e p ∈ J) : (0 : ZMod (2 ^ e - 1)) ∈ Lam e J := by
  haveI : NeZero e := ⟨by omega⟩
  exact ⟨cJ e J, fun p _ => cJ_mem_units e J p,
    (sum_cJ_mul_eq_zero e he J hJ).symm⟩

end CFSG.StandardType.ReeB2Fixed
