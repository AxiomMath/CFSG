module

public import CFSG.Quasithin.Background.F7TwoInvAutWrap

public section

namespace CFSG.Quasithin.F7Two

variable {L : Type*} [Group L]

theorem pow_two_pow_ne_one_of_pow {y : L} {s m : ℕ} (hm : Odd m)
    (h1 : y ^ (2 ^ s * m) = 1) (h2 : y ^ 2 ^ s ≠ 1) : ∀ n : ℕ, y ^ 2 ^ n ≠ 1 := by
  intro n hn
  apply h2
  have hz : (y ^ 2 ^ s) ^ m = 1 := by rw [← pow_mul]; exact h1
  have hw : (y ^ 2 ^ s) ^ 2 ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hn, one_pow]
  have hcop : Nat.Coprime m (2 ^ n) := Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hm)
  have h3 : (y ^ 2 ^ s) ^ Nat.gcd m (2 ^ n) = 1 := pow_gcd_eq_one.2 ⟨hz, hw⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem invAutGen_of_seeds {φ : MulAut L} {X : Set L} (hX : Subgroup.closure X = ⊤)
    (hX' : ∀ x ∈ X, x ∈ invXiAut φ ∨ φ x = x) (hne : ∃ x ∈ X, x ∈ invXiAut φ) :
    InvAutGen L φ := by
  obtain ⟨x₀, -, hx₀⟩ := hne
  rw [invAutGen_iff_closure_invXiAut, eq_top_iff, ← hX, Subgroup.closure_le]
  intro x hx
  rcases hX' x hx with h | h
  · exact Subgroup.subset_closure h
  · exact fixSubgroup_le_closure_invXiAut ⟨x₀, hx₀⟩ (mem_fixSubgroup_iff.mpr h)

theorem conj_conj_inv_apply (ψ : MulAut L) (d x : L) :
    (MulAut.conj d * ψ * (MulAut.conj d)⁻¹) x = d * ψ (d⁻¹ * x * d) * d⁻¹ := by
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem invAutGen_of_seeds_conj (ψ : MulAut L) (d : L) {X : Set L}
    (hX : Subgroup.closure X = ⊤)
    (hX' : ∀ x ∈ X, (∀ n : ℕ, (d * ψ (d⁻¹ * x * d) * d⁻¹ * x⁻¹) ^ 2 ^ n ≠ 1) ∨
      d * ψ (d⁻¹ * x * d) * d⁻¹ = x)
    (hne : ∃ x ∈ X, ∀ n : ℕ, (d * ψ (d⁻¹ * x * d) * d⁻¹ * x⁻¹) ^ 2 ^ n ≠ 1) :
    InvAutGen L ψ := by
  have key : ∀ x, x ∈ invXiAut (MulAut.conj d * ψ * (MulAut.conj d)⁻¹) ↔
      ∀ n : ℕ, (d * ψ (d⁻¹ * x * d) * d⁻¹ * x⁻¹) ^ 2 ^ n ≠ 1 := fun x => by
    rw [mem_invXiAut_iff, conj_conj_inv_apply]
  refine (InvAutGen.conj_iff (MulAut.conj d) ψ).2 (invAutGen_of_seeds hX ?_ ?_)
  · intro x hx
    rw [conj_conj_inv_apply, key]
    exact hX' x hx
  · obtain ⟨x, hx, h⟩ := hne
    exact ⟨x, hx, (key x).2 h⟩

theorem invAutGen_conj_of_seeds (r d : L) {X : Set L} (hX : Subgroup.closure X = ⊤)
    (hX' : ∀ x ∈ X, (∀ n : ℕ, ((d * r * d⁻¹) * x * (d * r * d⁻¹)⁻¹ * x⁻¹) ^ 2 ^ n ≠ 1) ∨
      (d * r * d⁻¹) * x = x * (d * r * d⁻¹))
    (hne : ∃ x ∈ X, ∀ n : ℕ, ((d * r * d⁻¹) * x * (d * r * d⁻¹)⁻¹ * x⁻¹) ^ 2 ^ n ≠ 1) :
    InvAutGen L (MulAut.conj r) := by
  have e : ∀ x : L, d * (MulAut.conj r) (d⁻¹ * x * d) * d⁻¹ = (d * r * d⁻¹) * x * (d * r * d⁻¹)⁻¹ :=
    fun x => by simp only [MulAut.conj_apply]; group
  refine invAutGen_of_seeds_conj (MulAut.conj r) d hX (fun x hx => ?_) ?_
  · rw [e]
    refine (hX' x hx).imp_right fun h => ?_
    rw [h]
    group
  · obtain ⟨x, hx, h⟩ := hne
    exact ⟨x, hx, by rw [e]; exact h⟩

theorem invAutGen_conj_of_conj {r x : L} (c : L) (hx : x = c * r * c⁻¹)
    (h : InvAutGen L (MulAut.conj r)) : InvAutGen L (MulAut.conj x) := by
  have e : MulAut.conj x = MulAut.conj c * MulAut.conj r * (MulAut.conj c)⁻¹ := by
    rw [hx, map_mul, map_mul, map_inv]
  rw [e]
  exact (InvAutGen.conj_iff (MulAut.conj c) (MulAut.conj r)).1 h

theorem mul_self_eq_one_of_conj_mul_self (hZ : Subgroup.center L = ⊥) {x : L}
    (h : MulAut.conj x * MulAut.conj x = 1) : x * x = 1 := by
  have hxx : x * x ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun a : MulAut L => a z) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
    have h2 : x * x * z * (x * x)⁻¹ = z := by
      calc x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
        _ = z := h1
    calc z * (x * x) = (x * x * z * (x * x)⁻¹) * (x * x) := by rw [h2]
      _ = x * x * z := by group
  rw [hZ, Subgroup.mem_bot] at hxx
  exact hxx

theorem invAutGen_of_inner_conj (hZ : Subgroup.center L = ⊥)
    (hin : ∀ φ : MulAut L, ∃ x : L, MulAut.conj x = φ)
    (h : ∀ x : L, x * x = 1 → x ≠ 1 → InvAutGen L (MulAut.conj x)) :
    ∀ φ : MulAut L, φ * φ = 1 → φ ≠ 1 → InvAutGen L φ := by
  intro φ hφ2 hφ1
  obtain ⟨x, rfl⟩ := hin φ
  refine h x (mul_self_eq_one_of_conj_mul_self hZ hφ2) ?_
  rintro rfl
  exact hφ1 (map_one _)

end CFSG.Quasithin.F7Two
