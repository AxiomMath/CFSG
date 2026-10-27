module

public import CFSG.RankThree.PartOne.K133C.InnerPlane

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix

section Flag

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def radFlag (v ψ : ι → K) (hψv : ψ ⬝ᵥ v = 0) : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K) *ᵥ v = v ∧
    (∀ y, ψ ⬝ᵥ ((g : Matrix ι ι K) *ᵥ y - y) = 0) ∧
    ∀ y, ψ ⬝ᵥ y = 0 → ∃ c : K, (g : Matrix ι ι K) *ᵥ y - y = c • v}
  one_mem' := ⟨by simp, fun y => by simp, fun y _ => ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨?_, fun y => ?_, fun y hy => ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hb1, ha1]
    · have h : ((a * b : GL ι K) : Matrix ι ι K) *ᵥ y - y =
          ((a : Matrix ι ι K) *ᵥ ((b : Matrix ι ι K) *ᵥ y) - (b : Matrix ι ι K) *ᵥ y) +
            ((b : Matrix ι ι K) *ᵥ y - y) := by
        rw [Units.val_mul, ← mulVec_mulVec]
        abel
      rw [h, dotProduct_add, ha2, hb2, add_zero]
    · obtain ⟨c₂, hc₂⟩ := hb3 y hy
      have hby : ψ ⬝ᵥ ((b : Matrix ι ι K) *ᵥ y) = 0 := by
        have h1 : (b : Matrix ι ι K) *ᵥ y = y + c₂ • v := by
          rw [← hc₂]; abel
        rw [h1, dotProduct_add, hy, dotProduct_smul, hψv, smul_zero, add_zero]
      obtain ⟨c₁, hc₁⟩ := ha3 _ hby
      refine ⟨c₁ + c₂, ?_⟩
      have h : ((a * b : GL ι K) : Matrix ι ι K) *ᵥ y - y =
          ((a : Matrix ι ι K) *ᵥ ((b : Matrix ι ι K) *ᵥ y) - (b : Matrix ι ι K) *ᵥ y) +
            ((b : Matrix ι ι K) *ᵥ y - y) := by
        rw [Units.val_mul, ← mulVec_mulVec]
        abel
      rw [h, hc₁, hc₂, add_smul]
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hinv : ((g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hinv' : (g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hgu : ∀ y, (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) = y := fun y => by
      rw [mulVec_mulVec, hinv', one_mulVec]
    refine ⟨?_, fun y => ?_, fun y hy => ?_⟩
    · calc ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
          = ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ v) := by rw [hg1]
        _ = v := by rw [mulVec_mulVec, hinv, one_mulVec]
    · set u := ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y with hu
      have h1 := hg2 u
      rw [hgu y] at h1
      have : u - y = -(y - u) := by abel
      show ψ ⬝ᵥ (u - y) = 0
      rw [this, dotProduct_neg, h1, neg_zero]
    · set u := ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y with hu
      have h1 := hg2 u
      rw [hgu y] at h1
      have hψu : ψ ⬝ᵥ u = 0 := by
        have : ψ ⬝ᵥ u = ψ ⬝ᵥ y - ψ ⬝ᵥ (y - u) := by rw [← dotProduct_sub]; congr 1; abel
        rw [this, hy, h1, sub_zero]
      obtain ⟨c, hc⟩ := hg3 u hψu
      rw [hgu y] at hc
      refine ⟨-c, ?_⟩
      show u - y = (-c) • v
      rw [neg_smul, ← hc]
      abel

theorem mem_radFlag {v ψ : ι → K} {hψv : ψ ⬝ᵥ v = 0} {g : GL ι K} :
    g ∈ radFlag v ψ hψv ↔ (g : Matrix ι ι K) *ᵥ v = v ∧
      (∀ y, ψ ⬝ᵥ ((g : Matrix ι ι K) *ᵥ y - y) = 0) ∧
      ∀ y, ψ ⬝ᵥ y = 0 → ∃ c : K, (g : Matrix ι ι K) *ᵥ y - y = c • v := Iff.rfl

theorem radFlag_cube {v ψ : ι → K} {hψv : ψ ⬝ᵥ v = 0} {g : GL ι K} (hg : g ∈ radFlag v ψ hψv) :
    ((g : Matrix ι ι K) - 1) * ((g : Matrix ι ι K) - 1) * ((g : Matrix ι ι K) - 1) = 0 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set N : Matrix ι ι K := (g : Matrix ι ι K) - 1 with hN
  have hNv : N *ᵥ v = 0 := by rw [hN, sub_mulVec, hg1, one_mulVec, sub_self]
  have hNy : ∀ y, N *ᵥ y = (g : Matrix ι ι K) *ᵥ y - y := fun y => by
    rw [hN, sub_mulVec, one_mulVec]
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
  have hψ1 : ψ ⬝ᵥ (N *ᵥ y) = 0 := by rw [hNy]; exact hg2 y
  obtain ⟨c, hc⟩ := hg3 (N *ᵥ y) hψ1
  have hc' : N *ᵥ (N *ᵥ y) = c • v := (hNy _).trans hc
  rw [hc', mulVec_smul, hNv, smul_zero]

theorem radFlag_pow_four [CharP K 2] {v ψ : ι → K} {hψv : ψ ⬝ᵥ v = 0} {g : GL ι K}
    (hg : g ∈ radFlag v ψ hψv) : g ^ 4 = 1 := by
  have hN3 := radFlag_cube hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set N : Matrix ι ι K := (g : Matrix ι ι K) - 1 with hN
  have hgN : (g : Matrix ι ι K) = 1 + N := by rw [hN]; abel
  have hN4 : N * N * N * N = 0 := by rw [hN3, zero_mul]
  have hsq : (1 + N) * (1 + N) = 1 + N * N := by
    have : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    rw [this, ← two_smul K N, h2, zero_smul, add_zero]
  have hfour : (g : Matrix ι ι K) ^ 4 = 1 := by
    have h4 : (g : Matrix ι ι K) ^ 4 = ((1 + N) * (1 + N)) * ((1 + N) * (1 + N)) := by
      rw [hgN]; noncomm_ring
    rw [h4, hsq]
    have : (1 + N * N) * (1 + N * N) = 1 + (N * N + N * N) + N * N * (N * N) := by
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    rw [this, ← two_smul K (N * N), h2, zero_smul, add_zero]
    have : N * N * (N * N) = N * N * N * N := by noncomm_ring
    rw [this, hN4, add_zero]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, hfour, Units.val_one])

theorem one_add_pow_of_cube_zero {N : Matrix ι ι K} (hN : N * N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : K) • N + ((k.choose 2 : ℕ) : K) • (N * N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have h3 : N * (N * N) = 0 := by rw [← mul_assoc]; exact hN
    have : (1 + (k : K) • N + ((k.choose 2 : ℕ) : K) • (N * N)) * (1 + N) =
        1 + N + (k : K) • N + (k : K) • (N * N) + ((k.choose 2 : ℕ) : K) • (N * N) +
          ((k.choose 2 : ℕ) : K) • (N * (N * N)) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, ← mul_assoc]
      abel
    rw [this, h3, smul_zero, add_zero, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    simp only [add_smul, one_smul]
    abel

theorem radFlag_eq_one_of_pow {p : ℕ} (hpK : (p : K) ≠ 0) {v ψ : ι → K} {hψv : ψ ⬝ᵥ v = 0}
    {g : GL ι K} (hg : g ∈ radFlag v ψ hψv) (hgp : g ^ p = 1) : g = 1 := by
  have hN3 := radFlag_cube hg
  set N : Matrix ι ι K := (g : Matrix ι ι K) - 1 with hN
  have hgN : (g : Matrix ι ι K) = 1 + N := by rw [hN]; abel
  have hpow : (g : Matrix ι ι K) ^ p = 1 := by
    have := congrArg (fun y : GL ι K => (y : Matrix ι ι K)) hgp
    simpa using this
  rw [hgN, one_add_pow_of_cube_zero hN3] at hpow
  have h1 : (p : K) • N + ((p.choose 2 : ℕ) : K) • (N * N) = 0 := by
    have := congrArg (fun M => M - 1) hpow
    simpa [add_assoc] using this
  have h2 : (p : K) • (N * N) = 0 := by
    have := congrArg (fun M => M * N) h1
    simp only [add_mul, smul_mul_assoc, zero_mul] at this
    rw [hN3, smul_zero, add_zero] at this
    exact this
  have h3 : N * N = 0 := (smul_eq_zero.1 h2).resolve_left hpK
  have h4 : (p : K) • N = 0 := by
    rw [h3, smul_zero, add_zero] at h1
    exact h1
  have h5 : N = 0 := (smul_eq_zero.1 h4).resolve_left hpK
  have : (g : Matrix ι ι K) = 1 := by rw [hgN, h5, add_zero]
  exact Units.ext (by rw [this, Units.val_one])

theorem radFlag_normalized {v ψ : ι → K} {hψv : ψ ⬝ᵥ v = 0} {h : GL ι K}
    (hv : (h : Matrix ι ι K) *ᵥ v = v) (hψ : ∀ y, ψ ⬝ᵥ ((h : Matrix ι ι K) *ᵥ y) = ψ ⬝ᵥ y)
    {g : GL ι K} (hg : g ∈ radFlag v ψ hψv) : h * g * h⁻¹ ∈ radFlag v ψ hψv := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hhi : ((h⁻¹ : GL ι K) : Matrix ι ι K) * (h : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hih : (h : Matrix ι ι K) * ((h⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hhy : ∀ y, (h : Matrix ι ι K) *ᵥ (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) = y := fun y => by
    rw [mulVec_mulVec, hih, one_mulVec]
  have hhiv : ((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
    calc ((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
        = ((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((h : Matrix ι ι K) *ᵥ v) := by rw [hv]
      _ = v := by rw [mulVec_mulVec, hhi, one_mulVec]
  have hψi : ∀ y, ψ ⬝ᵥ (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) = ψ ⬝ᵥ y := fun y => by
    have := hψ (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y)
    rw [hhy] at this
    exact this.symm
  have hconj : ∀ y, ((h * g * h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y - y =
      (h : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) -
        ((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) := fun y => by
    rw [mulVec_sub, hhy y, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  refine ⟨?_, fun y => ?_, fun y hy => ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hhiv, hg1, hv]
  · rw [hconj, hψ]
    exact hg2 _
  · have hyu : ψ ⬝ᵥ (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) = 0 := by rw [hψi]; exact hy
    obtain ⟨c, hc⟩ := hg3 _ hyu
    refine ⟨c, ?_⟩
    rw [hconj, hc, mulVec_smul, hv]

theorem exists_moved_of_family {p : ℕ} (hpK : (p : K) ≠ 0) {v ψ : ι → K} {hψv : ψ ⬝ᵥ v = 0}
    (P : Subgroup (GL ι K)) (hpow : ∀ h ∈ P, h ^ p = 1)
    (hfix : ∀ h ∈ P, (h : Matrix ι ι K) *ᵥ v = v)
    (hψ : ∀ h ∈ P, ∀ y, ψ ⬝ᵥ ((h : Matrix ι ι K) *ᵥ y) = ψ ⬝ᵥ y) (hP1 : ∃ h ∈ P, h ≠ 1)
    (e : (ι → K) → GL ι K)
    (he_conj : ∀ h ∈ P, ∀ w, ψ ⬝ᵥ w = 0 → h * e w * h⁻¹ = e ((h : Matrix ι ι K) *ᵥ w))
    (he_inj : ∀ w w', ψ ⬝ᵥ w = 0 → ψ ⬝ᵥ w' = 0 → e w = e w' → ∃ c : K, w' - w = c • v) :
    ∃ w, ψ ⬝ᵥ w = 0 ∧ ∃ h ∈ P, h * e w * h⁻¹ ≠ e w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₀, hh₀P, hh₀1⟩ := hP1
  apply hh₀1
  have hmem : h₀ ∈ radFlag v ψ hψv := by
    refine ⟨hfix h₀ hh₀P, fun y => ?_, fun y hy => ?_⟩
    · rw [dotProduct_sub, hψ h₀ hh₀P y, sub_self]
    · have h1 := hcon y hy h₀ hh₀P
      rw [he_conj h₀ hh₀P y hy] at h1
      have hψhy : ψ ⬝ᵥ ((h₀ : Matrix ι ι K) *ᵥ y) = 0 := by rw [hψ h₀ hh₀P y]; exact hy
      exact he_inj y _ hy hψhy h1.symm
  exact radFlag_eq_one_of_pow hpK hmem (hpow h₀ hh₀P)

end Flag

end CFSG.RankThree.PartOne.K133C
