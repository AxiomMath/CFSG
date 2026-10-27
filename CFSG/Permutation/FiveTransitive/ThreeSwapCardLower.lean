module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapCardLower

theorem eight_le {F : Type*} [Finite F] [DecidableEq F] (e : Fin 6 ↪ F) :
    8 ≤ Nat.card (ThreeSwapTwoGroup.subgroup e) := by
  let V := ThreeSwapTwoGroup.subgroup e
  let t0 := Equiv.swap (e 0) (e 1)
  let t1 := Equiv.swap (e 2) (e 3)
  let t2 := Equiv.swap (e 4) (e 5)
  have hm0 : t0 ∈ V := Subgroup.subset_closure (by simp [t0])
  have hm1 : t1 ∈ V := Subgroup.subset_closure (by simp [t1])
  have hm2 : t2 ∈ V := Subgroup.subset_closure (by simp [t2])
  let f : Bool × Bool × Bool → V := fun p =>
    ⟨(if p.1 then t0 else 1) * (if p.2.1 then t1 else 1) * (if p.2.2 then t2 else 1), by
      apply V.mul_mem
      · apply V.mul_mem
        · split <;> first | exact hm0 | exact V.one_mem
        · split <;> first | exact hm1 | exact V.one_mem
      · split <;> first | exact hm2 | exact V.one_mem⟩
  have h0 (p : Bool × Bool × Bool) : (f p).val (e 0) = if p.1 then e 1 else e 0 := by
    rcases p with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [f, t0, t1, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have h1 (p : Bool × Bool × Bool) : (f p).val (e 2) = if p.2.1 then e 3 else e 2 := by
    rcases p with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [f, t0, t1, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have h2 (p : Bool × Bool × Bool) : (f p).val (e 4) = if p.2.2 then e 5 else e 4 := by
    rcases p with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [f, t0, t1, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hf : Function.Injective f := by
    intro p q hpq
    have hp0 := congrArg (fun v : V => v.val (e 0)) hpq
    have hp1 := congrArg (fun v : V => v.val (e 2)) hpq
    have hp2 := congrArg (fun v : V => v.val (e 4)) hpq
    rw [h0, h0] at hp0
    rw [h1, h1] at hp1
    rw [h2, h2] at hp2
    have he0 : p.1 = q.1 := by
      cases hp : p.1 <;> cases hq : q.1 <;> simp_all [e.injective.eq_iff]
    have he1 : p.2.1 = q.2.1 := by
      cases hp : p.2.1 <;> cases hq : q.2.1 <;> simp_all [e.injective.eq_iff]
    have he2 : p.2.2 = q.2.2 := by
      cases hp : p.2.2 <;> cases hq : q.2.2 <;> simp_all [e.injective.eq_iff]
    exact Prod.ext he0 (Prod.ext he1 he2)
  have hle := Nat.card_le_card_of_injective f hf
  norm_num only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool] at hle
  exact hle

theorem eight_dvd {F : Type*} [Finite F] [DecidableEq F] (e : Fin 6 ↪ F) :
    8 ∣ Nat.card (ThreeSwapTwoGroup.subgroup e) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (ThreeSwapTwoGroup.isTwoGroup e).1.exists_card_eq
  have hle := eight_le e
  rw [hn] at hle ⊢
  have hn3 : 3 ≤ n := by
    by_contra h
    have hc : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hc with rfl | rfl | rfl <;> norm_num at hle
  exact pow_dvd_pow 2 hn3

end FiveTransitive.ThreeSwapCardLower

end CFSG
