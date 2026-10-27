module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgZ

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem torus_mul_apply (k₁ k₂ : Kˣ) (z : Coord J) :
    hermitianTorusAction J (k₁ * k₂) z =
      hermitianTorusAction J k₁ (hermitianTorusAction J k₂ z) := by
  have h1 : (k₁ : K) ≠ 0 := k₁.ne_zero
  have h2 : (k₂ : K) ≠ 0 := k₂.ne_zero
  have h3 : J.conj (k₁ : K) ≠ 0 := (map_ne_zero J.conj).2 h1
  have h4 : J.conj (k₂ : K) ≠ 0 := (map_ne_zero J.conj).2 h2
  apply coord_ext
  · rw [torus_fst, torus_fst, torus_fst, Units.val_mul, map_mul]; field_simp
  · rw [torus_snd, torus_snd, torus_snd, Units.val_mul, map_mul]; field_simp

theorem torus_one_apply (z : Coord J) : hermitianTorusAction J 1 z = z := by
  apply coord_ext
  · rw [torus_fst]; simp
  · rw [torus_snd]; simp

theorem torus_mul_hom (k : Kˣ) (z w : Coord J) :
    hermitianTorusAction J k (z * w) = hermitianTorusAction J k z * hermitianTorusAction J k w := by
  have h1 : (k : K) ≠ 0 := k.ne_zero
  have h3 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 h1
  apply coord_ext
  · rw [torus_fst, mul_fst, mul_fst, torus_fst, torus_fst]; ring
  · rw [torus_snd, mul_snd, mul_snd, torus_snd, torus_snd, torus_fst, torus_fst, map_mul,
      map_mul, map_pow, map_inv₀, conj_conj]
    field_simp

theorem torus_inv_hom (k : Kˣ) (z : Coord J) :
    hermitianTorusAction J k z⁻¹ = (hermitianTorusAction J k z)⁻¹ := by
  have h1 : (k : K) ≠ 0 := k.ne_zero
  have h3 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 h1
  apply coord_ext
  · rw [torus_fst, inv_fst, inv_fst, torus_fst]; ring
  · rw [torus_snd, inv_snd, inv_snd, torus_snd, map_mul, map_mul, map_inv₀, map_inv₀, conj_conj]
    ring

theorem torus_eq_one_of_forall {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
    (hcop : Nat.Coprime 3 (q + 1)) {k : Kˣ} (hk : ∀ z : Coord J, hermitianTorusAction J k z = z)
    {z₀ w₀ : Coord J} (hz₀ : z₀ ≠ 1) (hw₀ : w₀.1.1 ≠ 0) : k = 1 := by
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have hN : (k : K) * J.conj (k : K) = 1 := by
    have h := congrArg (fun v : Coord J => v.1.2) (hk z₀)
    change (hermitianTorusAction J k z₀).1.2 = z₀.1.2 at h
    rw [torus_snd] at h
    have hb := coord_snd_ne_zero J hz₀
    field_simp at h
    rw [mul_comm]; exact h.symm
  have h3 : (k : K) ^ 3 = 1 := by
    have h := congrArg (fun v : Coord J => v.1.1) (hk w₀)
    change (hermitianTorusAction J k w₀).1.1 = w₀.1.1 at h
    rw [torus_fst] at h
    have hck : J.conj (k : K) = (k : K)⁻¹ := eq_inv_of_mul_eq_one_right hN
    rw [hck, inv_inv] at h
    have : w₀.1.1 * (k : K) ^ 3 = w₀.1.1 * 1 := by linear_combination h
    exact mul_left_cancel₀ hw₀ this
  have hq1 : (k : K) ^ (q + 1) = 1 := by
    rw [pow_succ, ← hconj, mul_comm]; exact hN
  apply Units.ext
  have := (pow_gcd_eq_one (a := (k : K)) (m := 3) (n := q + 1)).mpr ⟨h3, hq1⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [Units.val_one]; exact this

end CFSG.UnitaryThreeRecognition.WeylAlg
