module

public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace CFSG.CoprimeFixedLift

theorem exists_fixed_mul_mem {G : Type*} [Group G] {b : G} (hb : b ^ 3 = 1) {N : Subgroup G}
    [Finite N] (hN : ¬ 3 ∣ Nat.card N) (hbN : ∀ n ∈ N, b * n * b⁻¹ ∈ N) {x : G}
    (hx : x⁻¹ * (b * x * b⁻¹) ∈ N) : ∃ n ∈ N, b * (x * n) * b⁻¹ = x * n := by
  let p : G := x⁻¹ * b * x
  have hp3 : p ^ 3 = 1 := by
    have h : p ^ 3 = x⁻¹ * b ^ 3 * x := by
      dsimp only [p]
      simpa only [inv_inv] using (conj_pow (a := x⁻¹) (b := b) (i := 3))
    rw [h, hb]
    simp
  have hb3 : b⁻¹ * b⁻¹ * b⁻¹ = 1 := by
    simpa only [pow_three'] using (show (b⁻¹) ^ 3 = 1 by rw [inv_pow, hb, inv_one])
  have hxN : x⁻¹ * b * x * b⁻¹ ∈ N := by
    simpa only [mul_assoc] using hx
  let f : N → N := fun n =>
    ⟨p * (n : G) * b⁻¹, by
      have h1 : b * (n : G) * b⁻¹ ∈ N := hbN n n.2
      have h2 : p * (n : G) * b⁻¹ = (x⁻¹ * b * x * b⁻¹) * (b * (n : G) * b⁻¹) := by
        dsimp only [p]
        group
      rw [h2]
      exact N.mul_mem hxN h1⟩
  have hp3' : p * p * p = 1 := by
    simpa only [pow_three'] using hp3
  have hf3 : ∀ n : N, f (f (f n)) = n := by
    intro n
    apply Subtype.ext
    change p * (p * (p * (n : G) * b⁻¹) * b⁻¹) * b⁻¹ = (n : G)
    calc p * (p * (p * (n : G) * b⁻¹) * b⁻¹) * b⁻¹
        = (p * p * p) * ((n : G) * (b⁻¹ * b⁻¹ * b⁻¹)) := by simp only [mul_assoc]
      _ = (n : G) := by rw [hp3', hb3]; simp
  let e : Equiv.Perm N :=
    { toFun := f
      invFun := fun n => f (f n)
      left_inv := hf3
      right_inv := hf3 }
  have he3 : e ^ 3 = 1 := by
    refine Equiv.Perm.ext fun n => ?_
    show (e ^ 3) n = n
    rw [Equiv.Perm.coe_pow]
    change f (f (f n)) = n
    exact hf3 n
  let H : Subgroup (Equiv.Perm N) := Subgroup.zpowers e
  have hHcard : Nat.card H ∣ 3 := by
    change Nat.card (Subgroup.zpowers e) ∣ 3
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
    exact he3
  have hH : IsPGroup 3 H :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hHcard)
  obtain ⟨n, hn⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (α := N) hN
  rw [MulAction.mem_fixedPoints] at hn
  have hfix : e • n = n := by
    simpa only [Subgroup.smul_def] using hn ⟨e, Subgroup.mem_zpowers e⟩
  have hfix' : x⁻¹ * b * x * (n : G) * b⁻¹ = (n : G) := by
    have hfn : e n = n := by simpa only [Equiv.Perm.smul_def] using hfix
    have hval := congrArg Subtype.val hfn
    simpa [e, f, p] using hval
  refine ⟨n, n.2, ?_⟩
  calc b * (x * (n : G)) * b⁻¹ = x * (x⁻¹ * b * x * (n : G) * b⁻¹) := by group
    _ = x * (n : G) := by rw [hfix']

end CFSG.CoprimeFixedLift

end
