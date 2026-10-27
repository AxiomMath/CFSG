module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzSporBasic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti

section Helpers

variable {G : Type*} [Group G]

theorem commute_of_involutions {p q : G} (hp : p * p = 1) (hq : q * q = 1)
    (h : (p * q) ^ 2 = 1) : Commute p q := by
  have hp' : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have h' : p * q = (p * q)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← sq]; exact h)
  rw [mul_inv_rev, hp', hq'] at h'
  exact h'

theorem commute_conj {p q : G} (h : Commute p q) (g : G) :
    Commute (g * p * g⁻¹) (g * q * g⁻¹) := by
  have := h.map (MulAut.conj g).toMonoidHom
  simpa [MulAut.conj_apply] using this

theorem commute_of_forall_eq_one {ι : Type*} {x : ι → G} (h : ∀ i, x i = 1) (i j : ι) :
    Commute (x i) (x j) := by
  rw [h i, h j]

end Helpers

section Torsion

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_mul_pow_three_eq_one (h3 : ¬ 3 ∣ Nat.card G) {x y : G} (hx : x ^ 2 = 1)
    (h : (x * y) ^ 3 = 1) : y = x := by
  have h1 := eq_one_of_pow_three_eq_one h3 h
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx)
  rw [← hx']
  exact eq_inv_of_mul_eq_one_right h1

omit [Finite G] in
theorem eq_one_of_pow_eq_one_of_coprime {x : G} {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1)
    (hmn : Nat.gcd m n = 1) : x = 1 := by
  have := pow_gcd_eq_one.2 ⟨hm, hn⟩
  rwa [hmn, pow_one] at this

end Torsion

theorem commute_of_two {P : GroupPresentation} (hP : P.generatorCount = 2) {G : Type*}
    [Group G] (x : Fin P.generatorCount → G)
    (h : Commute (x ⟨0, by omega⟩) (x ⟨1, by omega⟩)) (i j : Fin P.generatorCount) :
    Commute (x i) (x j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hi2 : i < 2 := hP ▸ hi
  have hj2 : j < 2 := hP ▸ hj
  interval_cases i <;> interval_cases j
  · exact Commute.refl _
  · exact h
  · exact h.symm
  · exact Commute.refl _

section Pair

variable {G : Type*} [Group G]

theorem commute_of_forall_eq_or_eq {ι : Type*} {x : ι → G} {u v : G} (huv : Commute u v)
    (h : ∀ i, x i = u ∨ x i = v) (i j : ι) : Commute (x i) (x j) := by
  rcases h i with hi | hi <;> rcases h j with hj | hj <;> rw [hi, hj] <;>
    first | exact huv | exact huv.symm

end Pair

section Center

variable {G : Type*} [Group G]

theorem eq_one_of_commute_two {P : GroupPresentation} (hP : P.generatorCount = 2)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (e : G ≃* P.Group) {z : G}
    (h0 : Commute z (presGen e ⟨0, by omega⟩)) (h1 : Commute z (presGen e ⟨1, by omega⟩)) :
    z = 1 := by
  refine eq_one_of_forall_commute hnab
    (commute_of_forall_commute_gen (closure_range_presGen e) fun k => ?_)
  obtain ⟨k, hk⟩ := k
  have hk2 : k < 2 := hP ▸ hk
  interval_cases k
  · exact h0
  · exact h1

end Center

macro "ks14_free" : tactic =>
  `(tactic| simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel,
    inv_mul_cancel, mul_one, one_mul, inv_inv, inv_one, mul_inv_rev])

section Pentagon

variable {G : Type*} [Group G]

theorem eq_one_of_pentagon {a c : G} (ha : a * a = 1) (hc : c ^ 5 = 1)
    (hac : (a * c) ^ 4 = 1) (hcomm : Commute a (c⁻¹ * a * c)) : c = 1 := by
  have hc4 : c * c * c * c * c = 1 := by
    rw [← hc]
    simp only [pow_succ, pow_zero, one_mul]
  have hac' : a * c * a * c * a * c * a * c = 1 := by
    rw [← hac]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hinv : ∀ g : G, (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := fun g => by
    rw [show g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ by ks14_free, ha]
    ks14_free
  have h01 : Commute (c * a * c⁻¹) a := by
    have key := commute_conj hcomm c
    rw [show c * (c⁻¹ * a * c) * c⁻¹ = a by ks14_free] at key
    exact key
  have h12 : Commute (c * c * a * c⁻¹ * c⁻¹) (c * a * c⁻¹) := by
    have key := commute_conj h01 c
    rw [show c * (c * a * c⁻¹) * c⁻¹ = c * c * a * c⁻¹ * c⁻¹ by ks14_free] at key
    exact key
  have h23 : Commute (c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹) (c * c * a * c⁻¹ * c⁻¹) := by
    have key := commute_conj h12 c
    rw [show c * (c * c * a * c⁻¹ * c⁻¹) * c⁻¹ = c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹ by ks14_free,
      show c * (c * a * c⁻¹) * c⁻¹ = c * c * a * c⁻¹ * c⁻¹ by ks14_free] at key
    exact key
  have hz3 : Commute (c⁻¹ * a * c) (c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹) := by
    have key := commute_conj hcomm c⁻¹
    have e : c⁻¹ * (c⁻¹ * a * c) * c⁻¹⁻¹ = c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹ := by
      calc c⁻¹ * (c⁻¹ * a * c) * c⁻¹⁻¹ =
          (c * c * c * c * c) * (c⁻¹ * c⁻¹ * a * c * c) * (c * c * c * c * c)⁻¹ := by
            rw [hc4]
            ks14_free
        _ = c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹ := by ks14_free
    rw [show c⁻¹ * a * c⁻¹⁻¹ = c⁻¹ * a * c by ks14_free, e] at key
    exact key
  obtain ⟨y1, hy1⟩ : ∃ y, y = c * a * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y, y = c * c * a * c⁻¹ * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨y3, hy3⟩ : ∃ y, y = c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ y, y = c⁻¹ * a * c := ⟨_, rfl⟩
  have hy1i : y1 * y1 = 1 := hy1 ▸ hinv c
  have hy2i : y2 * y2 = 1 := by
    rw [hy2, show c * c * a * c⁻¹ * c⁻¹ = (c * c) * a * (c * c)⁻¹ by ks14_free]
    exact hinv (c * c)
  have hy3i : y3 * y3 = 1 := by
    rw [hy3, show c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹ = (c * c * c) * a * (c * c * c)⁻¹ by ks14_free]
    exact hinv (c * c * c)
  rw [← hy1] at h01 h12
  rw [← hy2] at h12 h23
  rw [← hy3] at h23 hz3
  rw [← hz] at hz3 hcomm
  have hprod : a * y1 * y2 * y3 = c := by
    have h4 : a * c * a * c * a * c * a * c = a * y1 * y2 * y3 * (c * c * c * c) := by
      rw [hy1, hy2, hy3]
      group
    rw [h4, mul_eq_one_iff_eq_inv] at hac'
    rw [hac']
    calc (c * c * c * c)⁻¹ = (c * c * c * c * c)⁻¹ * c := by ks14_free
      _ = c := by rw [hc4, inv_one, one_mul]
  have hy1a : y1 * a * y1 = a := by
    rw [h01.eq, mul_assoc, hy1i, mul_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h1i : y1⁻¹ = y1 := inv_eq_of_mul_eq_one_right hy1i
  have h2i : y2⁻¹ = y2 := inv_eq_of_mul_eq_one_right hy2i
  have h3i : y3⁻¹ = y3 := inv_eq_of_mul_eq_one_right hy3i
  have hza : z = y3 * y2 * a * y2 * y3 := by
    rw [hz, ← hprod]
    have hpi : (a * y1 * y2 * y3)⁻¹ = y3 * y2 * y1 * a := by
      simp only [mul_inv_rev, hai, h1i, h2i, h3i, mul_assoc]
    rw [hpi]
    calc y3 * y2 * y1 * a * a * (a * y1 * y2 * y3) =
        y3 * y2 * (y1 * (a * a) * a * y1) * y2 * y3 := by ks14_free
      _ = y3 * y2 * (y1 * a * y1) * y2 * y3 := by rw [ha, mul_one]
      _ = y3 * y2 * a * y2 * y3 := by rw [hy1a]
  have hzb : z = y2 * a * y2 := by
    have e1 : z = y3 * z * y3 := by
      calc z = (y3 * y3) * z := by rw [hy3i, one_mul]
        _ = y3 * (y3 * z) := by ks14_free
        _ = y3 * (z * y3) := by rw [hz3.eq]
        _ = y3 * z * y3 := by ks14_free
    rw [e1, hza]
    calc y3 * (y3 * y2 * a * y2 * y3) * y3 = (y3 * y3) * y2 * a * y2 * (y3 * y3) := by ks14_free
      _ = y2 * a * y2 := by rw [hy3i, one_mul, mul_one]
  have h03 : Commute a y3 := by
    have h := hz3.eq
    rw [hzb] at h
    have h' : y2 * (y2 * a * y2 * y3) * y2 = y2 * (y3 * (y2 * a * y2)) * y2 := by rw [h]
    have e1 : y2 * (y2 * a * y2 * y3) * y2 = a * (y2 * y3 * y2) := by
      calc y2 * (y2 * a * y2 * y3) * y2 = (y2 * y2) * a * (y2 * y3 * y2) := by ks14_free
        _ = a * (y2 * y3 * y2) := by rw [hy2i, one_mul]
    have e2 : y2 * (y3 * (y2 * a * y2)) * y2 = (y2 * y3 * y2) * a := by
      calc y2 * (y3 * (y2 * a * y2)) * y2 = (y2 * y3 * y2) * a * (y2 * y2) := by ks14_free
        _ = (y2 * y3 * y2) * a := by rw [hy2i, mul_one]
    have e3 : y2 * y3 * y2 = y3 := by
      rw [← h23.eq, mul_assoc, hy2i, mul_one]
    rw [e1, e2, e3] at h'
    exact h'
  have h02 : Commute y2 a := by
    have key := commute_conj h03 (c * c)
    have e1 : c * c * a * (c * c)⁻¹ = y2 := by rw [hy2]; group
    have e2 : c * c * y3 * (c * c)⁻¹ = a := by
      rw [hy3]
      calc c * c * (c * c * c * a * c⁻¹ * c⁻¹ * c⁻¹) * (c * c)⁻¹ =
          (c * c * c * c * c) * a * (c * c * c * c * c)⁻¹ := by ks14_free
        _ = a := by rw [hc4, one_mul, inv_one, mul_one]
    rw [e1, e2] at key
    exact key
  have h13 : Commute y3 y1 := by
    have key := commute_conj h02 c
    have e1 : c * y2 * c⁻¹ = y3 := by rw [hy2, hy3]; group
    rw [e1, ← hy1] at key
    exact key
  have hcc : c * c = 1 := by
    rw [← hprod]
    have e : a * y1 * y2 * y3 * (a * y1 * y2 * y3) =
        (a * a) * (y1 * y1) * (y2 * y2) * (y3 * y3) := by
      calc a * y1 * y2 * y3 * (a * y1 * y2 * y3) =
          a * y1 * y2 * (y3 * a) * y1 * y2 * y3 := by ks14_free
        _ = a * y1 * y2 * (a * y3) * y1 * y2 * y3 := by rw [← h03.eq]
        _ = a * y1 * (y2 * a) * (y3 * y1) * y2 * y3 := by ks14_free
        _ = a * y1 * (a * y2) * (y1 * y3) * y2 * y3 := by rw [h02.eq, h13.eq]
        _ = a * (y1 * a) * y2 * y1 * (y3 * y2) * y3 := by ks14_free
        _ = a * (a * y1) * y2 * y1 * (y2 * y3) * y3 := by rw [h01.eq, h23.eq]
        _ = a * a * y1 * (y2 * y1) * y2 * (y3 * y3) := by ks14_free
        _ = a * a * y1 * (y1 * y2) * y2 * (y3 * y3) := by rw [h12.eq]
        _ = (a * a) * (y1 * y1) * (y2 * y2) * (y3 * y3) := by ks14_free
    rw [e, ha, hy1i, hy2i, hy3i]
    ks14_free
  calc c = (c * c * c * c * c) * (c * c)⁻¹ * (c * c)⁻¹ := by ks14_free
    _ = 1 := by rw [hc4, hcc]; ks14_free

end Pentagon

end CFSG.RankThree.PartTwo.KFacts.KS14
