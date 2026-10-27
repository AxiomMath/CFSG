module

public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Quasithin.S153D

open scoped commutatorElement

section Pair

variable {Q : Type*} [Group Q]

theorem conj_commutator' (ρ X Y : Q) :
    ρ * ⁅X, Y⁆ * ρ⁻¹ = ⁅ρ * X * ρ⁻¹, ρ * Y * ρ⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_central_left {X Y c : Q} (hcY : c * Y = Y * c) : ⁅X * c, Y⁆ = ⁅X, Y⁆ := by
  simp only [commutatorElement_def]
  have h1 : c * Y * c⁻¹ = Y := by rw [hcY]; group
  calc X * c * Y * (X * c)⁻¹ * Y⁻¹ = X * (c * Y * c⁻¹) * X⁻¹ * Y⁻¹ := by group
    _ = X * Y * X⁻¹ * Y⁻¹ := by rw [h1]

theorem comm_mul_central_right {X Y c : Q} (hcX : c * X = X * c) : ⁅X, Y * c⁆ = ⁅X, Y⁆ := by
  simp only [commutatorElement_def]
  have h1 : c * X⁻¹ * c⁻¹ = X⁻¹ := by
    have : c * X⁻¹ = X⁻¹ * c := by
      calc c * X⁻¹ = X⁻¹ * (X * c) * X⁻¹ := by group
        _ = X⁻¹ * (c * X) * X⁻¹ := by rw [hcX]
        _ = X⁻¹ * c := by group
    rw [this]; group
  calc X * (Y * c) * X⁻¹ * (Y * c)⁻¹ = X * Y * (c * X⁻¹ * c⁻¹) * Y⁻¹ := by group
    _ = X * Y * X⁻¹ * Y⁻¹ := by rw [h1]

theorem comm_inv_left {A B : Q} (hzA : ⁅A, B⁆ * A = A * ⁅A, B⁆) : ⁅A⁻¹, B⁆ = ⁅A, B⁆⁻¹ := by
  have e : ⁅A⁻¹, B⁆ = A⁻¹ * ⁅A, B⁆⁻¹ * A := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have : ⁅A, B⁆⁻¹ * A = A * ⁅A, B⁆⁻¹ := by
    calc ⁅A, B⁆⁻¹ * A = ⁅A, B⁆⁻¹ * (A * ⁅A, B⁆) * ⁅A, B⁆⁻¹ := by group
      _ = ⁅A, B⁆⁻¹ * (⁅A, B⁆ * A) * ⁅A, B⁆⁻¹ := by rw [hzA]
      _ = A * ⁅A, B⁆⁻¹ := by group
  rw [mul_assoc, this]
  group

theorem comm_inv_right {A B : Q} (hzB : ⁅A, B⁆ * B = B * ⁅A, B⁆) : ⁅A, B⁻¹⁆ = ⁅A, B⁆⁻¹ := by
  have e : ⁅A, B⁻¹⁆ = B⁻¹ * ⁅A, B⁆⁻¹ * B := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have : ⁅A, B⁆⁻¹ * B = B * ⁅A, B⁆⁻¹ := by
    calc ⁅A, B⁆⁻¹ * B = ⁅A, B⁆⁻¹ * (B * ⁅A, B⁆) * ⁅A, B⁆⁻¹ := by group
      _ = ⁅A, B⁆⁻¹ * (⁅A, B⁆ * B) * ⁅A, B⁆⁻¹ := by rw [hzB]
      _ = B * ⁅A, B⁆⁻¹ := by group
  rw [mul_assoc, this]
  group

theorem conj_comm_of_inv_left {A B ρ cA cB : Q}
    (hzA : ⁅A, B⁆ * A = A * ⁅A, B⁆) (hcAB : cA * B = B * cA) (hcAcB : cA * cB = cB * cA)
    (hcBA : cB * A⁻¹ = A⁻¹ * cB)
    (hA : ρ * A * ρ⁻¹ = A⁻¹ * cA) (hB : ρ * B * ρ⁻¹ = B * cB) :
    ρ * ⁅A, B⁆ * ρ⁻¹ = ⁅A, B⁆⁻¹ := by
  rw [conj_commutator', hA, hB]
  have hcA' : cA * (B * cB) = (B * cB) * cA := by
    calc cA * (B * cB) = (cA * B) * cB := by group
      _ = (B * cA) * cB := by rw [hcAB]
      _ = B * (cA * cB) := by group
      _ = B * (cB * cA) := by rw [hcAcB]
      _ = (B * cB) * cA := by group
  rw [comm_mul_central_left hcA', comm_mul_central_right hcBA]
  exact comm_inv_left hzA

theorem conj_comm_of_inv_right {A B ρ cB : Q}
    (hzB : ⁅A, B⁆ * B = B * ⁅A, B⁆) (hcBA : cB * A = A * cB)
    (hA : ρ * A * ρ⁻¹ = A) (hB : ρ * B * ρ⁻¹ = B⁻¹ * cB) :
    ρ * ⁅A, B⁆ * ρ⁻¹ = ⁅A, B⁆⁻¹ := by
  rw [conj_commutator', hA, hB, comm_mul_central_right hcBA]
  exact comm_inv_right hzB

theorem eq_one_of_eq_inv_of_cube {z : Q} (h3 : z ^ 3 = 1) (h : z = z⁻¹) : z = 1 := by
  have h2 : z * z = 1 := by
    calc z * z = z * z⁻¹ := by rw [← h]
      _ = 1 := by group
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem mem_of_sq_mem {N : Subgroup Q} {x : Q} (h3 : x ^ 3 = 1) (h : x * x ∈ N) : x ∈ N := by
  have h4 : (x * x) * (x * x) = x ^ 3 * x := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have : x = (x * x) * (x * x) := by
    rw [h4, h3, one_mul]
  rw [this]
  exact N.mul_mem h h

theorem mem_of_commutator_inv {N : Subgroup Q} {y ρ c : Q} (hy3 : y ^ 3 = 1)
    (hc : c * y = y * c) (hcN : c ∈ N)
    (h : ρ * y * ρ⁻¹ = y⁻¹ * c) (hN : y * ρ * y⁻¹ * ρ⁻¹ ∈ N) : y ∈ N := by
  have e1 : y * ρ * y⁻¹ * ρ⁻¹ = y * (ρ * y * ρ⁻¹)⁻¹ := by group
  rw [e1, h] at hN
  have hcy : c⁻¹ * y = y * c⁻¹ := by
    calc c⁻¹ * y = c⁻¹ * (y * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * y) * c⁻¹ := by rw [hc]
      _ = y * c⁻¹ := by group
  have e2 : y * (y⁻¹ * c)⁻¹ = (y * y) * c⁻¹ := by
    calc y * (y⁻¹ * c)⁻¹ = y * (c⁻¹ * y) := by group
      _ = y * (y * c⁻¹) := by rw [hcy]
      _ = (y * y) * c⁻¹ := by group
  rw [e2] at hN
  have : y * y ∈ N := by
    have := N.mul_mem hN hcN
    simpa using this
  exact mem_of_sq_mem hy3 this

theorem sign_eq_one {Zs : Subgroup Q} {A B ρ cA cB : Q} {e₁ e₂ : ℤ}
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (hA3 : A ^ 3 = 1) (hz3 : ⁅A, B⁆ ^ 3 = 1) (hz1 : ⁅A, B⁆ ≠ 1)
    (hAZ : A ∉ Zs) (hcA : cA ∈ Zs)
    (hcBA : cB * A = A * cB) (hzB : ⁅A, B⁆ * B = B * ⁅A, B⁆)
    (hρA : ρ * A * ρ⁻¹ = A ^ e₂ * cA) (hρB : ρ * B * ρ⁻¹ = B ^ e₁ * cB)
    (hρA' : ρ * A * ρ⁻¹ = A) (hρz : ρ * ⁅A, B⁆ * ρ⁻¹ = ⁅A, B⁆) :
    e₁ = 1 ∧ e₂ = 1 := by
  have he₂1 : e₂ = 1 := by
    rcases he₂ with h | h
    · exact h
    · exfalso
      rw [h, zpow_neg_one] at hρA
      have h1 : A = A⁻¹ * cA := hρA'.symm.trans hρA
      have h2 : A * A = cA := by
        calc A * A = A * (A⁻¹ * cA) := by rw [← h1]
          _ = cA := by group
      exact hAZ (mem_of_sq_mem hA3 (h2 ▸ hcA))
  refine ⟨?_, he₂1⟩
  rcases he₁ with h | h
  · exact h
  · exfalso
    rw [h, zpow_neg_one] at hρB
    have := conj_comm_of_inv_right hzB hcBA hρA' hρB
    rw [hρz] at this
    exact hz1 (eq_one_of_eq_inv_of_cube hz3 this)

theorem commute_of_gen {Ys Zs : Subgroup Q} {A B : Q}
    (hZY : Zs ≤ Ys) (hAY : A ∈ Ys) (hBY : B ∈ Ys) (hAB : A * B = B * A)
    (hcen : ∀ c ∈ Zs, ∀ w ∈ Ys, c * w = w * c)
    (hgen : ∀ y ∈ Ys, ∃ (i j : ℤ), ∃ c ∈ Zs, y = B ^ i * A ^ j * c) :
    ∀ x ∈ Ys, ∀ y ∈ Ys, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, j, c, hc, rfl⟩ := hgen x hx
  obtain ⟨i', j', c', hc', rfl⟩ := hgen y hy
  have h1 : Commute A B := hAB
  have hBB := (Commute.refl B).zpow_zpow i i'
  have hBA := h1.symm.zpow_zpow i j'
  have hAB' := h1.zpow_zpow j i'
  have hAA := (Commute.refl A).zpow_zpow j j'
  have huu : Commute (B ^ i * A ^ j) (B ^ i' * A ^ j') :=
    (hBB.mul_right hBA).mul_left (hAB'.mul_right hAA)
  have hu : B ^ i * A ^ j ∈ Ys := Ys.mul_mem (Ys.zpow_mem hBY i) (Ys.zpow_mem hAY j)
  have hu' : B ^ i' * A ^ j' ∈ Ys := Ys.mul_mem (Ys.zpow_mem hBY i') (Ys.zpow_mem hAY j')
  have huc' : Commute (B ^ i * A ^ j) c' := (hcen c' hc' _ hu).symm
  have hcu' : Commute c (B ^ i' * A ^ j') := hcen c hc _ hu'
  have hcc' : Commute c c' := hcen c hc c' (hZY hc')
  exact ((huu.mul_right huc').mul_left (hcu'.mul_right hcc')).eq

theorem pow_mem_of_mul_of_pow {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {x q d : H}
    {k : ℕ} (hq : q ∈ N) (hd : d ^ 2 ^ k = 1) (hx : x = q * d) : x ^ 2 ^ k ∈ N := by
  have h1 : (QuotientGroup.mk (x ^ 2 ^ k) : H ⧸ N) = 1 := by
    rw [QuotientGroup.mk_pow, hx, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff q).2 hq, one_mul,
      ← QuotientGroup.mk_pow, hd, QuotientGroup.mk_one]
  exact (QuotientGroup.eq_one_iff _).1 h1

end Pair

end CFSG.Quasithin.S153D
