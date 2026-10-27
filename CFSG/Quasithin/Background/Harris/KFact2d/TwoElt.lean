module

public import CFSG.Quasithin.Background.Harris.KFact2d.OddCore

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_mem_of_two_part {D J Q : Subgroup G} (hQn : D ≤ Subgroup.normalizer (Q : Set G))
    (hJD : J ≤ D) (hJc : ∀ x ∈ J, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hodd : ∀ y ∈ J, (∃ k : ℕ, y ^ 2 ^ k ∈ Q) → y ∈ Q) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hc : a * b * a⁻¹ * b⁻¹ ∈ J) (m : ℕ) (hm : a ^ 2 ^ m ∈ J) : a * b * a⁻¹ * b⁻¹ ∈ Q := by
  haveI := normal_subgroupOf_of_le_normalizer hQn
  let φ : ↥D →* ↥D ⧸ Q.subgroupOf D := QuotientGroup.mk' (Q.subgroupOf D)
  have hcD : a * b * a⁻¹ * b⁻¹ ∈ D := hJD hc
  have hcentral : ∀ x (hx : x ∈ J), ∀ e : ↥D ⧸ Q.subgroupOf D,
      φ ⟨x, hJD hx⟩ * e = e * φ ⟨x, hJD hx⟩ := by
    intro x hx e
    induction e using QuotientGroup.induction_on with
    | H y =>
      show φ ⟨x, hJD hx⟩ * φ y = φ y * φ ⟨x, hJD hx⟩
      have h := hJc x hx (y : G) y.2
      have h1 : ⁅φ ⟨x, hJD hx⟩, φ y⁆ = 1 := by
        rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rw [QuotientGroup.mk'_apply] at *
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using h
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
  set A : ↥D ⧸ Q.subgroupOf D := φ ⟨a, ha⟩ with hA
  set B : ↥D ⧸ Q.subgroupOf D := φ ⟨b, hb⟩ with hB
  set C : ↥D ⧸ Q.subgroupOf D := φ ⟨a * b * a⁻¹ * b⁻¹, hcD⟩ with hC
  have hCc : ∀ e, C * e = e * C := hcentral _ hc
  have hAB : A * B = C * (B * A) := by
    rw [hA, hB, hC, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  have hind : ∀ k : ℕ, A ^ k * B = C ^ k * B * A ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc A ^ (k + 1) * B = A ^ k * (A * B) := by rw [pow_succ, mul_assoc]
        _ = A ^ k * (C * (B * A)) := by rw [hAB]
        _ = (A ^ k * C) * (B * A) := by rw [mul_assoc]
        _ = (C * A ^ k) * (B * A) := by rw [← hCc]
        _ = C * (A ^ k * B) * A := by simp only [mul_assoc]
        _ = C * (C ^ k * B * A ^ k) * A := by rw [ih]
        _ = C ^ (k + 1) * B * A ^ (k + 1) := by
          rw [pow_succ', pow_succ]
          simp only [mul_assoc]
  have hAn : A ^ 2 ^ m * B = B * A ^ 2 ^ m := by
    have h := hcentral (a ^ 2 ^ m) hm B
    have : φ ⟨a ^ 2 ^ m, hJD hm⟩ = A ^ 2 ^ m := by
      rw [hA, ← map_pow]
      rfl
    rwa [this] at h
  have h1 := hind (2 ^ m)
  have h2 : C ^ 2 ^ m * B * A ^ 2 ^ m = 1 * B * A ^ 2 ^ m := by
    rw [← h1, hAn, one_mul]
  have h3 : C ^ 2 ^ m = 1 := by
    have := mul_right_cancel h2
    simpa using this
  have h4 : (a * b * a⁻¹ * b⁻¹) ^ 2 ^ m ∈ Q := (mk_pow_eq_one_iff hQn hcD _).mp h3
  exact hodd _ hc ⟨m, h4⟩

end CFSG.Quasithin.Background.Harris.KFact2d
