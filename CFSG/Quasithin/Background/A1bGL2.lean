module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.ZMod

public section

open Matrix

namespace CFSG.Quasithin

namespace A1b

namespace GL2


variable {F : Type*} [Field F]

theorem cayley_hamilton_two (m : Matrix (Fin 2) (Fin 2) F) :
    m * m = m.trace • m - m.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

theorem smul_one_eq_one_or_neg {s : F} (h : (s • (1 : Matrix (Fin 2) (Fin 2) F)) *
    (s • (1 : Matrix (Fin 2) (Fin 2) F)) = 1) :
    s • (1 : Matrix (Fin 2) (Fin 2) F) = 1 ∨ s • (1 : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have h1 : s * s = 1 := by
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rcases mul_self_eq_one_iff.1 h1 with rfl | rfl
  · left; simp
  · right; simp

theorem eq_one_or_neg_one_of_trace_ne_zero {a : Matrix (Fin 2) (Fin 2) F} (ha : a * a = 1)
    (ht : a.trace ≠ 0) : a = 1 ∨ a = -1 := by
  have hCH := cayley_hamilton_two a
  rw [ha] at hCH
  have h3 : a.trace • a = (1 + a.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have := hCH
    rw [eq_sub_iff_add_eq] at this
    rw [← this, add_smul, one_smul]
  have hal : a = ((1 + a.det) / a.trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc a = a.trace⁻¹ • (a.trace • a) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = a.trace⁻¹ • ((1 + a.det) • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [h3]
      _ = ((1 + a.det) / a.trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [smul_smul, div_eq_inv_mul]
  rw [hal] at ha ⊢
  exact smul_one_eq_one_or_neg ha

theorem trace_eq_zero_of_sq_eq_one {a : Matrix (Fin 2) (Fin 2) F} (ha : a * a = 1)
    (h1 : a ≠ 1) (h1' : a ≠ -1) : a.trace = 0 := by
  by_contra ht
  rcases eq_one_or_neg_one_of_trace_ne_zero ha ht with h | h
  · exact h1 h
  · exact h1' h

theorem mul_self_eq_one_of_smul_one {s : F}
    (h : (s * s) • (1 : Matrix (Fin 2) (Fin 2) F) = 1) : s * s = 1 := by
  have := congrFun (congrFun h 0) 0
  simpa using this

theorem eq_or_eq_neg_of_commute (h2 : (2 : F) ≠ 0) {a a' : Matrix (Fin 2) (Fin 2) F}
    (ha : a * a = 1) (ha' : a' * a' = 1) (hc : a * a' = a' * a) (h1 : a ≠ 1) (h1' : a ≠ -1)
    (h2' : a' ≠ 1) (h2'' : a' ≠ -1) : a' = a ∨ a' = -a := by
  have ht := trace_eq_zero_of_sq_eq_one ha h1 h1'
  have ht' := trace_eq_zero_of_sq_eq_one ha' h2' h2''
  have hCH := cayley_hamilton_two (a + a')
  have htc : (a + a').trace = 0 := by rw [Matrix.trace_add, ht, ht', add_zero]
  rw [htc, zero_smul, zero_sub] at hCH
  have hsq : (a + a') * (a + a') = (2 : F) • (1 + a * a') := by
    calc (a + a') * (a + a') = a * a + a * a' + a' * a + a' * a' := by
          rw [add_mul, mul_add, mul_add]; abel
      _ = (2 : F) • (1 + a * a') := by rw [ha, ha', ← hc, two_smul]; abel
  set d := (a + a').det with hd
  have h3 : (2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) + (2 : F) • (a * a') =
      -(d • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    rw [← smul_add, ← hsq, hCH]
  have h4 : (2 : F) • (a * a') = (-d - 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [eq_sub_of_add_eq' h3, sub_smul, neg_smul]
  set s : F := (-d - 2) / 2 with hs
  have h5 : a * a' = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc a * a' = (2 : F)⁻¹ • ((2 : F) • (a * a')) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = s • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [h4, smul_smul, hs, div_eq_inv_mul]
  have h6 : a' = s • a := by
    calc a' = (a * a) * a' := by rw [ha, one_mul]
      _ = a * (a * a') := by rw [mul_assoc]
      _ = s • a := by rw [h5, mul_smul_comm, mul_one]
  have h7 : s * s = 1 := by
    apply mul_self_eq_one_of_smul_one
    calc (s * s) • (1 : Matrix (Fin 2) (Fin 2) F) = (s * s) • (a * a) := by rw [ha]
      _ = (s • a) * (s • a) := by rw [smul_mul_smul_comm]
      _ = a' * a' := by rw [← h6]
      _ = 1 := ha'
  rcases mul_self_eq_one_iff.1 h7 with h8 | h8
  · left
    rw [h6, h8, one_smul]
  · right
    rw [h6, h8, neg_smul, one_smul]

theorem mul_neg_one_mul {R : Type*} [CommRing R] (u v : Matrix (Fin 2) (Fin 2) R) :
    u * (-1) * v = -(u * v) := by
  rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul]

theorem mul_neg_mul {R : Type*} [CommRing R] (u w v : Matrix (Fin 2) (Fin 2) R) :
    u * (-w) * v = -(u * w * v) := by
  rw [Matrix.mul_neg, Matrix.neg_mul]

section GLTwo

variable {p : ℕ} [Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h'
  exact hp2 this

theorem conj_eq_or_neg (hp2 : p ≠ 2) {A : Subgroup (GL (Fin 2) (ZMod p))}
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : GL (Fin 2) (ZMod p)} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) {b : GL (Fin 2) (ZMod p)}
    (hb : b ∈ A) :
    ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (b : Matrix (Fin 2) (Fin 2) (ZMod p)) ∨
      ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        -(b : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  have hmat : ∀ x ∈ A, (x : Matrix (Fin 2) (Fin 2) (ZMod p)) * (x : Matrix (Fin 2) (Fin 2) (ZMod p))
      = 1 := fun x hx => by
    have := congrArg (fun y : GL (Fin 2) (ZMod p) => (y : Matrix (Fin 2) (Fin 2) (ZMod p)))
      (hA2 x hx)
    simpa using this
  have hgg : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * (g⁻¹ : GL (Fin 2) (ZMod p)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcoe : ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * (b : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (g⁻¹ : GL (Fin 2) (ZMod p)) := by simp
  have e1 : ∀ (u v : Matrix (Fin 2) (Fin 2) (ZMod p)), u * (-1) * v = -(u * v) := by
    intro u v
    exact mul_neg_one_mul u v
  by_cases h1 : (b : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
  · left
    rw [hcoe, h1, mul_one, hgg]
  by_cases h1' : (b : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1
  · left
    rw [hcoe, h1', e1, hgg]
  have hb' := hg b hb
  have hc : (b : Matrix (Fin 2) (Fin 2) (ZMod p)) * ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) =
      ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (b : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    have := congrArg (fun y : GL (Fin 2) (ZMod p) => (y : Matrix (Fin 2) (Fin 2) (ZMod p)))
      (hAc b hb _ hb')
    simpa using this
  have hgi : (g⁻¹ : GL (Fin 2) (ZMod p)) * g = 1 := inv_mul_cancel g
  have hback : ∀ c : GL (Fin 2) (ZMod p), (g * c * g⁻¹ : GL (Fin 2) (ZMod p)) = 1 → c = 1 := by
    intro c hc
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [hc]; group
  have h2 : ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ 1 := by
    intro h
    have : (g * b * g⁻¹ : GL (Fin 2) (ZMod p)) = 1 := Units.ext (by simpa using h)
    exact h1 (by rw [hback b this, Units.val_one])
  have h2' : ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) ≠ -1 := by
    intro h
    apply h1'
    have hb_eq : (b : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((g * b * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (g : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      have : b = g⁻¹ * (g * b * g⁻¹) * g := by group
      calc (b : Matrix (Fin 2) (Fin 2) (ZMod p)) =
            ((g⁻¹ * (g * b * g⁻¹) * g : GL (Fin 2) (ZMod p)) :
              Matrix (Fin 2) (Fin 2) (ZMod p)) := by
            rw [← this]
        _ = _ := by simp
    have hgi' : ((g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 := by
      rw [← Units.val_mul, hgi, Units.val_one]
    rw [hb_eq, h, e1, hgi']
  exact eq_or_eq_neg_of_commute (two_ne_zero_zmod hp2) (hmat b hb) (hmat _ hb') hc h1 h1' h2 h2'

theorem centralizes_of_odd_order (hp2 : p ≠ 2) {A : Subgroup (GL (Fin 2) (ZMod p))}
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {g : GL (Fin 2) (ZMod p)} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hodd : Odd (orderOf g))
    {a : GL (Fin 2) (ZMod p)} (ha : a ∈ A) : g * a = a * g := by
  have hkey := conj_eq_or_neg hp2 hA2 hAc hg ha
  have e2 : ∀ u w v : Matrix (Fin 2) (Fin 2) (ZMod p), u * (-w) * v = -(u * w * v) := fun u w v =>
    mul_neg_mul u w v
  have h2 : g * (g * a * g⁻¹) * g⁻¹ = a := by
    apply Units.ext
    have hcoe : ((g * (g * a * g⁻¹) * g⁻¹ : GL (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          ((g * a * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (g⁻¹ : GL (Fin 2) (ZMod p)) := by simp
    have hcoe' : ((g * a * g⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * (a : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          (g⁻¹ : GL (Fin 2) (ZMod p)) := by simp
    rw [hcoe]
    rcases hkey with h | h
    · rw [h, ← hcoe']
      exact h
    · rw [h, e2, ← hcoe', h]
      exact neg_neg _
  have h3 : g * g * a * (g * g)⁻¹ = a := by
    calc g * g * a * (g * g)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by group
      _ = a := h2
  have h4 : Commute (g * g) a := by
    exact mul_inv_eq_iff_eq_mul.1 h3
  obtain ⟨k, hk⟩ := hodd
  have hgk : g = (g * g) ^ (k + 1) := by
    have h5 : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    calc g = g ^ (2 * k + 1) * g := by rw [h5, one_mul]
      _ = g ^ (2 * k + 2) := by rw [← pow_succ]
      _ = (g * g) ^ (k + 1) := by rw [← sq, ← pow_mul]; ring_nf
  have h6 : Commute g a := by
    rw [hgk]
    exact Commute.pow_left h4 (k + 1)
  exact h6.eq

end GLTwo


end GL2

end A1b

end CFSG.Quasithin
