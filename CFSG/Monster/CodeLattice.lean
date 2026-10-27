module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster

@[expose] def bitLift (t : ZMod 2) : ℤ := t.val

theorem bitLift_zero_or_one (t : ZMod 2) : bitLift t = 0 ∨ bitLift t = 1 := by
  fin_cases t <;> decide

@[expose] def weight (d : Fin 24 → ZMod 2) : ℤ := ∑ i, bitLift (d i)

@[expose] def allOnes : Fin 24 → ZMod 2 := fun _ => 1

@[expose] def codeLattice (C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) : Set (Fin 24 → ℤ) :=
  {u | ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ d ∈ C,
    (∀ i, u i ≡ m + 2 * bitLift (d i) [ZMOD 4]) ∧ ∑ i, u i ≡ 4 * m [ZMOD 8]}

@[expose] def codeForm (u v : Fin 24 → ℚ) : ℚ := (∑ i, u i * v i) / 8

theorem bitLift_add (a b : ZMod 2) : bitLift (a + b) = (bitLift a + bitLift b) % 2 := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitLift_add_one (a : ZMod 2) : bitLift (a + 1) = 1 - bitLift a := by
  fin_cases a <;> decide

theorem bitLift_one : bitLift 1 = 1 := rfl

variable {C : Submodule (ZMod 2) (Fin 24 → ZMod 2)}

theorem zero_mem_codeLattice : (0 : Fin 24 → ℤ) ∈ codeLattice C :=
  ⟨0, .inl rfl, 0, C.zero_mem, fun i => by simp [bitLift], by simp⟩

theorem add_mem_codeLattice (hΩ : allOnes ∈ C) {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (hv : v ∈ codeLattice C) : u + v ∈ codeLattice C := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  obtain ⟨m', hm', d', hd', hvd, hvs⟩ := hv
  have hsum : ∑ i, (u + v) i = ∑ i, u i + ∑ i, v i := by simp [Finset.sum_add_distrib]
  by_cases h2 : m = 1 ∧ m' = 1
  · obtain ⟨rfl, rfl⟩ := h2
    refine ⟨0, .inl rfl, d + d' + allOnes, C.add_mem (C.add_mem hd hd') hΩ, fun i => ?_, ?_⟩
    · have h1 := hud i
      have h1' := hvd i
      simp only [Pi.add_apply, allOnes, bitLift_add, bitLift_one]
      unfold Int.ModEq at h1 h1' ⊢
      have ha := bitLift_zero_or_one (d i)
      have hb := bitLift_zero_or_one (d' i)
      omega
    · rw [hsum]
      have h := hus.add hvs
      unfold Int.ModEq at h ⊢
      omega
  · refine ⟨m + m', ?_, d + d', C.add_mem hd hd', fun i => ?_, ?_⟩
    · omega
    · have h1 := hud i
      have h1' := hvd i
      simp only [Pi.add_apply, bitLift_add]
      unfold Int.ModEq at h1 h1' ⊢
      have ha := bitLift_zero_or_one (d i)
      have hb := bitLift_zero_or_one (d' i)
      omega
    · rw [hsum]
      have h := hus.add hvs
      unfold Int.ModEq at h ⊢
      omega

theorem neg_mem_codeLattice (hΩ : allOnes ∈ C) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    -u ∈ codeLattice C := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  have hsum : ∑ i, (-u) i = -∑ i, u i := by simp [Finset.sum_neg_distrib]
  rcases hm with rfl | rfl
  · refine ⟨0, .inl rfl, d, hd, fun i => ?_, ?_⟩
    · have h1 := hud i
      simp only [Pi.neg_apply]
      unfold Int.ModEq at h1 ⊢
      have ha := bitLift_zero_or_one (d i)
      omega
    · rw [hsum]
      unfold Int.ModEq at hus ⊢
      omega
  · refine ⟨1, .inr rfl, d + allOnes, C.add_mem hd hΩ, fun i => ?_, ?_⟩
    · have h1 := hud i
      simp only [Pi.neg_apply, Pi.add_apply, allOnes, bitLift_add_one]
      unfold Int.ModEq at h1 ⊢
      have ha := bitLift_zero_or_one (d i)
      omega
    · rw [hsum]
      unfold Int.ModEq at hus ⊢
      omega

@[expose] def codeLatticeSubgroup (hΩ : allOnes ∈ C) : AddSubgroup (Fin 24 → ℤ) where
  carrier := codeLattice C
  zero_mem' := zero_mem_codeLattice
  add_mem' := add_mem_codeLattice hΩ
  neg_mem' := neg_mem_codeLattice hΩ

theorem smul_eight_mem_codeLattice (x : Fin 24 → ℤ) : (8 : ℤ) • x ∈ codeLattice C := by
  refine ⟨0, .inl rfl, 0, C.zero_mem, fun i => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bitLift, ZMod.val_zero, Nat.cast_zero,
      mul_zero, add_zero]
    exact (Int.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right (by norm_num) _))
  · simp only [Pi.smul_apply, smul_eq_mul, mul_zero, ← Finset.mul_sum]
    exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)

theorem sum_mul_self_emod_sixteen (hC4 : ∀ d ∈ C, weight d % 4 = 0) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : (∑ i, u i * u i) % 16 = 0 := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  set b : Fin 24 → ℤ := fun i => bitLift (d i) with hbdef
  have hb : ∀ i, b i = 0 ∨ b i = 1 := fun i => bitLift_zero_or_one (d i)
  set k : Fin 24 → ℤ := fun i => (u i - m - 2 * b i) / 4 with hkdef
  have huk : ∀ i, u i = m + 2 * b i + 4 * k i := by
    intro i
    have h := hud i
    unfold Int.ModEq at h
    simp only [hkdef, hbdef]
    omega
  have hsq : ∀ i, u i * u i =
      m + 4 * b i + 16 * (k i * k i) + 4 * m * b i + 8 * m * k i + 16 * (b i * k i) := by
    intro i
    rw [huk i]
    have hm2 : m * m = m := by rcases hm with rfl | rfl <;> norm_num
    have hb2 : b i * b i = b i := by rcases hb i with h | h <;> rw [h] <;> norm_num
    linear_combination hm2 + 4 * hb2
  have hw : weight d = ∑ i, b i := rfl
  have hw4 : (∑ i, b i) % 4 = 0 := hw ▸ hC4 d hd
  have hsum : ∑ i, u i = 24 * m + 2 * ∑ i, b i + 4 * ∑ i, k i := by
    rw [Finset.sum_congr rfl (fun i _ => huk i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  have hsq_sum : ∑ i, u i * u i = 24 * m + 4 * ∑ i, b i + 16 * ∑ i, (k i * k i) +
      4 * m * ∑ i, b i + 8 * m * ∑ i, k i + 16 * ∑ i, (b i * k i) := by
    rw [Finset.sum_congr rfl (fun i _ => hsq i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  rw [hsq_sum]
  unfold Int.ModEq at hus
  rw [hsum] at hus
  rcases hm with rfl | rfl
  · simp only [zero_mul, add_zero, mul_zero] at hus ⊢
    omega
  · simp only [mul_one] at hus ⊢
    omega

theorem sum_mul_emod_eight (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    (∑ i, u i * v i) % 8 = 0 := by
  have h1 := sum_mul_self_emod_sixteen hC4 (add_mem_codeLattice hΩ hu hv)
  have h2 := sum_mul_self_emod_sixteen hC4 hu
  have h3 := sum_mul_self_emod_sixteen hC4 hv
  have e : ∑ i, (u + v) i * (u + v) i =
      ∑ i, u i * u i + ∑ i, v i * v i + 2 * ∑ i, u i * v i := by
    simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h1
  omega

theorem codeForm_even_integral (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    (∃ n : ℤ, codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 2 * n) ∧
      ∃ n : ℤ, codeForm (fun i => (u i : ℚ)) (fun i => (v i : ℚ)) = n := by
  obtain ⟨a, ha⟩ : ∃ a, ∑ i, u i * u i = 16 * a :=
    ⟨(∑ i, u i * u i) / 16, by have := sum_mul_self_emod_sixteen hC4 hu; omega⟩
  obtain ⟨c, hc⟩ : ∃ c, ∑ i, u i * v i = 8 * c :=
    ⟨(∑ i, u i * v i) / 8, by have := sum_mul_emod_eight hΩ hC4 hu hv; omega⟩
  refine ⟨⟨a, ?_⟩, ⟨c, ?_⟩⟩
  · unfold codeForm
    have : (∑ i, (u i : ℚ) * (u i : ℚ)) = ((∑ i, u i * u i : ℤ) : ℚ) := by push_cast; rfl
    rw [this, ha]
    push_cast
    ring
  · unfold codeForm
    have : (∑ i, (u i : ℚ) * (v i : ℚ)) = ((∑ i, u i * v i : ℤ) : ℚ) := by push_cast; rfl
    rw [this, hc]
    push_cast
    ring

end CFSG.Monster
