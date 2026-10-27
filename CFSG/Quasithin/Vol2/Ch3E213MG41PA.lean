module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

variable {F K : Type*} [Field F] [CharP F 2] [Field K] [Algebra F K]

@[expose] def bil2 (x y : F × F) : F := x.1 * y.2 + x.2 * y.1

@[expose] def IsCocycle2 (b : F × F → K) : Prop :=
  ∀ x y : F × F, bil2 x y ≠ 0 → b (x + bil2 x y • y) = b x + algebraMap F K (bil2 x y) * b y

theorem sq_ne_one_char2 {μ : F} (hμ1 : μ ≠ 1) : μ ^ 2 ≠ 1 := by
  intro h
  apply hμ1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (μ - 1) ^ 2 = 0 := by linear_combination h - μ * h2 + h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

theorem eq_zero_of_isCocycle2 (hsq : ∀ a : F, ∃ r : F, r ^ 2 = a) {μ : F} (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ 1) {b : F × F → K} (hb : IsCocycle2 b) (h₁ : b (1, 0) = 0) (h₂ : b (0, 1) = 0)
    (h₃ : b (μ ^ 2, 0) = 0) {x : F × F} (hx : x ≠ 0) : b x = 0 := by
  set ι := algebraMap F K with hι
  have I1 : ∀ s t : F, s ≠ 0 → t ≠ 0 → b (s * t ^ 2, s) = b (0, s) + ι (s * t) * b (t, 0) := by
    intro s t hs ht
    have hne : bil2 ((0 : F), s) (t, 0) ≠ 0 := by simp [bil2, hs, ht]
    have h := hb (0, s) (t, 0) hne
    have e1 : ((0 : F), s) + bil2 ((0 : F), s) (t, 0) • (t, (0 : F)) = (s * t ^ 2, s) := by
      simp only [bil2, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> ring
    have e2 : bil2 ((0 : F), s) (t, 0) = s * t := by simp [bil2]
    rw [e1, e2] at h
    exact h
  have I2 : ∀ u t : F, u ≠ 0 → t ≠ 0 → b (u, u * t ^ 2) = b (u, 0) + ι (u * t) * b (0, t) := by
    intro u t hu ht
    have hne : bil2 (u, (0 : F)) (0, t) ≠ 0 := by simp [bil2, hu, ht]
    have h := hb (u, 0) (0, t) hne
    have e1 : (u, (0 : F)) + bil2 (u, (0 : F)) (0, t) • ((0 : F), t) = (u, u * t ^ 2) := by
      simp only [bil2, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> ring
    have e2 : bil2 (u, (0 : F)) (0, t) = u * t := by simp [bil2]
    rw [e1, e2] at h
    exact h
  have E : ∀ s v : F, s ≠ 0 → v ≠ 0 →
      b (0, s) + ι (s * v) * b (v, 0) = b (s * v ^ 2, 0) + ι (s * v) * b (0, v⁻¹) := by
    intro s v hs hv
    have h1 := I1 s v hs hv
    have h2 := I2 (s * v ^ 2) v⁻¹ (mul_ne_zero hs (pow_ne_zero 2 hv)) (inv_ne_zero hv)
    have e1 : s * v ^ 2 * v⁻¹ ^ 2 = s := by field_simp
    have e2 : s * v ^ 2 * v⁻¹ = s * v := by field_simp
    rw [e1, e2] at h2
    rw [← h1, h2]
  have E1 : ∀ s : F, s ≠ 0 → b (0, s) = b (s, 0) := by
    intro s hs
    have h := E s 1 hs one_ne_zero
    simpa only [mul_one, one_pow, inv_one, h₁, h₂, mul_zero, add_zero] using h
  have E5 : ∀ s v : F, s ≠ 0 → v ≠ 0 → b (s, 0) = b (s * v ^ 2, 0) - ι s * b (v ^ 2, 0) := by
    intro s v hs hv
    have h3 := E s v hs hv
    have h4 := E 1 v one_ne_zero hv
    rw [E1 s hs, E1 v⁻¹ (inv_ne_zero hv)] at h3
    rw [E1 1 one_ne_zero, E1 v⁻¹ (inv_ne_zero hv), h₁, one_mul, one_mul] at h4
    rw [map_mul] at h3
    linear_combination h3 - ι s * h4
  have hμ2 : 1 - ι (μ ^ 2) ≠ 0 := by
    rw [← map_one ι, ← map_sub]
    exact (map_ne_zero ι).mpr (sub_ne_zero.mpr (Ne.symm (sq_ne_one_char2 hμ1)))
  have hB : ∀ s : F, s ≠ 0 → b (s, 0) = 0 := by
    intro s hs
    obtain ⟨r, hr⟩ := hsq s
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hs (by rw [← hr]; ring)
    have h6 := E5 s μ hs hμ0
    rw [h₃, mul_zero, sub_zero] at h6
    have h7 := E5 (μ ^ 2) r (pow_ne_zero 2 hμ0) hr0
    rw [h₃, hr, mul_comm (μ ^ 2) s, ← h6] at h7
    have h8 : (1 - ι (μ ^ 2)) * b (s, 0) = 0 := by linear_combination -h7
    rcases mul_eq_zero.mp h8 with h | h
    · exact absurd h hμ2
    · exact h
  obtain ⟨u, s⟩ := x
  by_cases hs : s = 0
  · subst hs
    have hu : u ≠ 0 := fun hu => hx (by rw [hu]; rfl)
    exact hB u hu
  · by_cases hu : u = 0
    · subst hu
      rw [E1 s hs]
      exact hB s hs
    · obtain ⟨t, ht⟩ := hsq (u / s)
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hu (by rw [zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at ht; tauto)
      have h := I1 s t hs ht0
      have e : s * t ^ 2 = u := by rw [ht]; field_simp
      rw [e, E1 s hs, hB s hs, hB t ht0, mul_zero, add_zero] at h
      exact h

omit [CharP F 2] in
theorem IsCocycle2.sub {b c : F × F → K} (hb : IsCocycle2 b) (hc : IsCocycle2 c) :
    IsCocycle2 (fun x => b x - c x) := by
  intro x y h
  simp only [hb x y h, hc x y h]
  ring

omit [CharP F 2] in
theorem IsCocycle2.add_mul {b c : F × F → K} (hb : IsCocycle2 b) (hc : IsCocycle2 c) (θ : K) :
    IsCocycle2 (fun x => b x + θ * c x) := by
  intro x y h
  simp only [hb x y h, hc x y h]
  ring

omit [CharP F 2] in
theorem isCocycle2_lin (A B : K) :
    IsCocycle2 (fun x : F × F => algebraMap F K x.1 * A + algebraMap F K x.2 * B) := by
  intro x y _
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_add,
    map_mul]
  ring

theorem eq_of_sq_eq_char2 {a c : F} (h : a ^ 2 = c ^ 2) : a = c := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (a - c) ^ 2 = 0 := by linear_combination h + (c ^ 2 - a * c) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

theorem isCocycle2_h {r : F → F} (hr : ∀ a, r a ^ 2 = a) :
    IsCocycle2 (fun x : F × F => 1 + algebraMap F K (r (x.1 * x.2))) := by
  intro x y _
  set c := bil2 x y with hc
  have hc' : c = x.1 * y.2 + x.2 * y.1 := hc
  have key : r ((x + c • y).1 * (x + c • y).2) = r (x.1 * x.2) + c * r (y.1 * y.2) + c := by
    apply eq_of_sq_eq_char2
    rw [hr]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hx := hr (x.1 * x.2)
    have hy := hr (y.1 * y.2)
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (-1) * hx + (-c ^ 2) * hy + (-c) * hc' +
      (-(r (x.1 * x.2) * c * r (y.1 * y.2) + r (x.1 * x.2) * c + c ^ 2 * r (y.1 * y.2))) * h2
  simp only [key, map_add, map_mul]
  ring

theorem exists_eq_lin_add_h (hsq : ∀ a : F, ∃ r : F, r ^ 2 = a) {r : F → F}
    (hr : ∀ a, r a ^ 2 = a) {μ : F} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) {b : F × F → K}
    (hb : IsCocycle2 b) :
    ∃ A B θ : K, ∀ x : F × F, x ≠ 0 → b x = algebraMap F K x.1 * A + algebraMap F K x.2 * B +
      θ * (1 + algebraMap F K (r (x.1 * x.2))) := by
  set ι := algebraMap F K with hι
  have hr0 : r 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp ((hr 0).trans rfl)
  have hμ2 : 1 - ι (μ ^ 2) ≠ 0 := by
    rw [← map_one ι, ← map_sub]
    exact (map_ne_zero ι).mpr (sub_ne_zero.mpr (Ne.symm (sq_ne_one_char2 hμ1)))
  set A := (b (1, 0) - b (μ ^ 2, 0)) / (1 - ι (μ ^ 2)) with hA
  set θ := b (1, 0) - A with hθ
  set B := b (0, 1) - θ with hB
  refine ⟨A, B, θ, fun x hx => ?_⟩
  have hc := hb.sub ((isCocycle2_lin A B).add_mul (isCocycle2_h hr) θ)
  have h0 := eq_zero_of_isCocycle2 hsq hμ0 hμ1 hc ?_ ?_ ?_ hx
  · exact sub_eq_zero.mp h0
  · simp only [mul_zero, hr0, map_zero, add_zero, map_one, one_mul, mul_one]
    rw [hθ]
    ring
  · simp only [zero_mul, hr0, map_zero, add_zero, map_one, one_mul, zero_add]
    rw [hB]
    ring
  · simp only [mul_zero, hr0, map_zero, add_zero, mul_one]
    rw [hθ, hA]
    field_simp
    ring

end CFSG.Quasithin.Ch3E213M.G41.Big
