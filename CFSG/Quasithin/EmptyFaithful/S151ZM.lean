module

public import CFSG.Quasithin.Background.FLcFlagU

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ}

@[expose] def TCond (n a : ℕ) (g : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ p q : Fin n, ¬ ((p : ℕ) < a ∧ a ≤ (q : ℕ)) → g p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q

@[expose] def BCond (n a : ℕ) (g : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ p q : Fin n, a ≤ (p : ℕ) → (q : ℕ) < a → g p q = 0

theorem tcond_sub_mul_sub {a : ℕ} {g h : Matrix (Fin n) (Fin n) (ZMod 2)} (hg : TCond n a g)
    (hh : TCond n a h) : (g - 1) * (h - 1) = 0 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : (p : ℕ) < a ∧ a ≤ (m : ℕ)
  · by_cases h2 : (m : ℕ) < a ∧ a ≤ (q : ℕ)
    · omega
    · simp only [Matrix.sub_apply, hh m q h2, sub_self, mul_zero]
  · simp only [Matrix.sub_apply, hg p m h1, sub_self, zero_mul]

theorem tcond_mul {a : ℕ} {g h : Matrix (Fin n) (Fin n) (ZMod 2)} (hg : TCond n a g)
    (hh : TCond n a h) : TCond n a (g * h) := by
  have hXY := tcond_sub_mul_sub hg hh
  have hgh : g * h = 1 + (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  intro p q hpq
  rw [hgh, hXY]
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.sub_apply, hg p q hpq, hh p q hpq,
    sub_self, add_zero]

theorem tcond_sq {a : ℕ} {g : Matrix (Fin n) (Fin n) (ZMod 2)} (hg : TCond n a g) :
    g * g = 1 := by
  have hXY := tcond_sub_mul_sub hg hg
  have hgg : g * g = 1 + (g - 1) + (g - 1) + (g - 1) * (g - 1) := by noncomm_ring
  rw [hgg, hXY]
  ext p q
  simp only [Matrix.add_apply, Matrix.zero_apply, add_zero]
  have h1 : (g - 1) p q + (g - 1) p q = 0 := CharTwo.add_self_eq_zero _
  rw [add_assoc, h1, add_zero]

@[expose] def Tgrp (n a : ℕ) : Subgroup (SLt n) where
  carrier := {g | TCond n a (mat g)}
  one_mem' := by
    intro p q _
    rw [mat_one]
  mul_mem' := fun {g h} hg hh => by
    show TCond n a (mat (g * h))
    rw [mat_mul]
    exact tcond_mul hg hh
  inv_mem' := fun {g} hg => by
    have hgg := tcond_sq hg
    have hinv : mat g⁻¹ = mat g := by
      have h1 : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
      calc mat g⁻¹ = mat g⁻¹ * (mat g * mat g) := by rw [hgg, mul_one]
        _ = (mat g⁻¹ * mat g) * mat g := by rw [mul_assoc]
        _ = mat g := by rw [h1, one_mul]
    show TCond n a (mat g⁻¹)
    rw [hinv]
    exact hg

theorem Tgrp_sq {a : ℕ} {g : SLt n} (hg : g ∈ Tgrp n a) : g * g = 1 := by
  have h1 : mat (g * g) = mat 1 := by
    rw [mat_mul, mat_one]
    exact tcond_sq hg
  exact Subtype.ext h1

theorem Tgrp_le_Ut (a : ℕ) : Tgrp n a ≤ Ut n := by
  intro g hg
  rw [Ut, mem_unitriangular]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h1 : mat g i j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j := hg i j (by omega)
    exact h1.trans (Matrix.one_apply_ne (ne_of_gt hji))
  · have h1 : mat g i i = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i i := hg i i (by omega)
    exact h1.trans (by simp)

theorem bcond_of_mem_stabilizer {a : ℕ} {g : SLt n} (h : g ∈ stabilizer (flagSpace n (ZMod 2) a)) :
    BCond n a (mat g) := by
  intro p q hp hq
  have hv : (Pi.single q (1 : ZMod 2) : Fin n → ZMod 2) ∈ flagSpace n (ZMod 2) a := by
    rw [mem_flagSpace]
    intro j hj
    have hjq : j ≠ q := fun he => by rw [he] at hj; omega
    simp [hjq]
  have h1 := (mem_stabilizer_iff.mp h _).mp hv
  rw [mem_flagSpace] at h1
  have h2 := h1 p hp
  rwa [Matrix.mulVec_single_one] at h2

theorem Tgrp_conj {a : ℕ} {h : SLt n} (hb : BCond n a (mat h)) (hb' : BCond n a (mat h⁻¹))
    {g : SLt n} (hg : g ∈ Tgrp n a) : h * g * h⁻¹ ∈ Tgrp n a := by
  have e : mat (h * g * h⁻¹) = 1 + mat h * (mat g - 1) * mat h⁻¹ := by
    have h1 : mat h * mat h⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
    rw [mat_mul, mat_mul]
    calc mat h * mat g * mat h⁻¹ = mat h * mat h⁻¹ + mat h * (mat g - 1) * mat h⁻¹ := by
          noncomm_ring
      _ = 1 + mat h * (mat g - 1) * mat h⁻¹ := by rw [h1]
  intro p q hpq
  show mat (h * g * h⁻¹) p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q
  rw [e]
  simp only [Matrix.add_apply]
  have hz : (mat h * (mat g - 1) * mat h⁻¹) p q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m' _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases h1 : (m : ℕ) < a ∧ a ≤ (m' : ℕ)
    · by_cases hp : a ≤ (p : ℕ)
      · rw [hb p m hp h1.1, zero_mul, zero_mul]
      · by_cases hq : (q : ℕ) < a
        · rw [hb' m' q h1.2 hq, mul_zero]
        · exact absurd ⟨by omega, by omega⟩ hpq
    · have hX : (mat g - 1) m m' = 0 := by
        simp only [Matrix.sub_apply, hg m m' h1, sub_self]
      rw [hX, mul_zero, zero_mul]
  rw [hz, add_zero]

@[expose] def tvec (j k : Fin n) (hjk : j ≠ k) : SLt n :=
  ⟨Matrix.transvection j k (1 : ZMod 2), Matrix.det_transvection_of_ne j k hjk 1⟩

theorem mat_tvec (j k : Fin n) (hjk : j ≠ k) :
    mat (tvec j k hjk) = 1 + Matrix.single j k (1 : ZMod 2) := rfl

theorem tvec_mem_Tgrp {a : ℕ} {j k : Fin n} (hj : (j : ℕ) < a) (hk : a ≤ (k : ℕ))
    (hjk : j ≠ k) : tvec j k hjk ∈ Tgrp n a := by
  intro p q hpq
  show mat (tvec j k hjk) p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q
  rw [mat_tvec, Matrix.add_apply, Matrix.single_apply]
  have : ¬ (j = p ∧ k = q) := by
    rintro ⟨rfl, rfl⟩
    exact hpq ⟨hj, hk⟩
  simp [this]

theorem mem_Tgrp_of_commute {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a < n) {g : SLt n}
    (hc : ∀ t ∈ Tgrp n a, g * t = t * g) : g ∈ Tgrp n a := by
  have rel : ∀ j k : Fin n, (j : ℕ) < a → a ≤ (k : ℕ) → ∀ p q : Fin n,
      mat g p j * (if k = q then 1 else 0) = (if j = p then 1 else 0) * mat g k q := by
    intro j k hj hk p q
    have hjk : j ≠ k := fun h => by rw [h] at hj; omega
    have h1 := hc (tvec j k hjk) (tvec_mem_Tgrp hj hk hjk)
    have h2 : mat (g * tvec j k hjk) = mat (tvec j k hjk * g) := congrArg (fun x => mat x) h1
    rw [mat_mul, mat_mul, mat_tvec] at h2
    have h3 : mat g * Matrix.single j k (1 : ZMod 2) = Matrix.single j k 1 * mat g := by
      rw [mul_add, add_mul, mul_one, one_mul] at h2
      exact add_left_cancel h2
    have h4 := congrFun (congrFun h3 p) q
    simp only [Matrix.mul_apply, Matrix.single_apply] at h4
    have e1 : (∑ x : Fin n, mat g p x * if j = x ∧ k = q then (1 : ZMod 2) else 0) =
        mat g p j * (if k = q then 1 else 0) := by
      by_cases hkq : k = q
      · simp [hkq]
      · simp [hkq]
    have e2 : (∑ x : Fin n, (if j = p ∧ k = x then (1 : ZMod 2) else 0) * mat g x q) =
        (if j = p then 1 else 0) * mat g k q := by
      by_cases hjp : j = p
      · simp [hjp]
      · simp [hjp]
    rw [e1, e2] at h4
    exact h4
  have hn0 : 0 < n := by omega
  let j₀ : Fin n := ⟨0, hn0⟩
  let k₀ : Fin n := ⟨a, ha2⟩
  have hj₀ : (j₀ : ℕ) < a := by show 0 < a; omega
  have hk₀ : a ≤ (k₀ : ℕ) := le_rfl
  have hA : ∀ j k : Fin n, (j : ℕ) < a → a ≤ (k : ℕ) → ∀ p : Fin n,
      mat g p j = (if j = p then 1 else 0) * mat g k k := by
    intro j k hj hk p
    have := rel j k hj hk p k
    simpa using this
  have hB : ∀ j k : Fin n, (j : ℕ) < a → a ≤ (k : ℕ) → ∀ q : Fin n,
      mat g k q = mat g j j * (if k = q then 1 else 0) := by
    intro j k hj hk q
    have := rel j k hj hk j q
    simpa using this.symm
  have hdet : (mat g).det = 1 := g.2
  have hkk : ∀ k : Fin n, a ≤ (k : ℕ) → mat g k k = 1 := by
    intro k hk
    by_contra hne
    have h0 : mat g k k = 0 := by
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (mat g k k) with h | h
      · exact h
      · exact absurd h hne
    have hz : (mat g).det = 0 := by
      refine Matrix.det_eq_zero_of_column_eq_zero j₀ fun p => ?_
      rw [hA j₀ k hj₀ hk p, h0, mul_zero]
    rw [hdet] at hz
    exact one_ne_zero hz
  have hjj : ∀ j : Fin n, (j : ℕ) < a → mat g j j = 1 := by
    intro j hj
    rw [hA j k₀ hj hk₀ j, hkk k₀ hk₀]
    simp
  intro p q hpq
  show mat g p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q
  rw [Matrix.one_apply]
  by_cases hp : (p : ℕ) < a
  · have hq : (q : ℕ) < a := by
      by_contra hq
      exact hpq ⟨hp, by omega⟩
    rw [hA q k₀ hq hk₀ p, hkk k₀ hk₀, mul_one]
    by_cases hpq' : p = q
    · simp [hpq']
    · have : ¬ q = p := fun h => hpq' h.symm
      simp [hpq', this]
  · have hp' : a ≤ (p : ℕ) := by omega
    rw [hB j₀ p hj₀ hp' q, hjj j₀ hj₀, one_mul]

end CFSG.Quasithin.FLc
