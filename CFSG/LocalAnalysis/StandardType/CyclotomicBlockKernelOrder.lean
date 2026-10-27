module

public import Mathlib
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorusMonomial

public section

namespace CFSG.StandardType

open Matrix
open CFSG.HardMathSupport.Lang.TwE6Step3 (monoHom monoHom_apply monoHom_monoHom)

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma smul_sq_sub_one_mul_smul_sub_one {P : Matrix ι ι ℤ} (hP : P * P + P + 1 = 0)
    (q : ℤ) :
    (q • (P * P) - 1) * (q • P - 1) = (q ^ 2 + q + 1) • (1 : Matrix ι ι ℤ) := by
  have hPP : P * P = -(P + 1) := eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
  have hP3 : P * P * P = 1 := by
    rw [hPP, neg_mul, add_mul, one_mul, hPP]
    abel
  have e1 : (q • (P * P) - 1) * (q • P - 1) =
      (q ^ 2) • (P * P * P) - q • (P * P + P) + 1 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
    module
  rw [e1, hP3, hPP]
  module

theorem det_smul_sub_one_sq {P G : Matrix ι ι ℤ} (hP : P * P + P + 1 = 0)
    (hG : Pᵀ * G * P = G) (hdet : G.det ≠ 0) (q : ℤ) :
    (q • P - 1).det ^ 2 = (q ^ 2 + q + 1) ^ Fintype.card ι := by
  have hPP : P * P = -(P + 1) := eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
  have hP3 : P * P * P = 1 := by
    rw [hPP, neg_mul, add_mul, one_mul, hPP]
    abel
  have hBA := smul_sq_sub_one_mul_smul_sub_one hP q
  have hPtG : Pᵀ * G = G * (P * P) := by
    calc Pᵀ * G = Pᵀ * G * 1 := (mul_one _).symm
      _ = Pᵀ * G * (P * P * P) := by rw [hP3]
      _ = (Pᵀ * G * P) * (P * P) := by simp only [mul_assoc]
      _ = G * (P * P) := by rw [hG]
  have hGB : G * (q • (P * P) - 1) = (q • P - 1)ᵀ * G := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    rw [mul_sub, mul_one, sub_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul, hPtG]
  have hdetB : (q • (P * P) - 1).det = (q • P - 1).det := by
    have h := congrArg Matrix.det hGB
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    rw [mul_comm (q • P - 1).det G.det] at h
    exact mul_left_cancel₀ hdet h
  calc (q • P - 1).det ^ 2
      = (q • (P * P) - 1).det * (q • P - 1).det := by rw [hdetB, pow_two]
    _ = ((q • (P * P) - 1) * (q • P - 1)).det := (Matrix.det_mul _ _).symm
    _ = ((q ^ 2 + q + 1) • (1 : Matrix ι ι ℤ)).det := by rw [hBA]
    _ = (q ^ 2 + q + 1) ^ Fintype.card ι := by
        rw [Matrix.det_smul, Matrix.det_one, mul_one]

theorem pow_eq_one_of_mem_ker_monoHom {G : Type*} [CommGroup G] {A B : Matrix ι ι ℤ} {N : ℤ}
    (hBA : B * A = N • 1) {c : ι → G} (hc : monoHom A c = 1) (i : ι) : c i ^ N = 1 := by
  have h1 : monoHom B (monoHom A c) = monoHom (B * A) c := monoHom_monoHom B A c
  rw [hc, map_one, hBA] at h1
  have h2 := congrFun h1 i
  simp only [monoHom_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at h2
  rw [Finset.prod_eq_single i] at h2
  · simpa using h2.symm
  · intro j _ hji
    simp [hji.symm]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem natCard_ker_monoHom {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : Matrix ι ι ℤ)
    (hA : (A.det : Ω) ≠ 0) : Nat.card (monoHom (G := Ωˣ) A).ker = A.det.natAbs := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℤ := A.submatrix e.symm e.symm
  have hA'det : A'.det = A.det := Matrix.det_submatrix_equiv_self e.symm A
  have hA' : (A'.det : Ω) ≠ 0 := by rw [hA'det]; exact hA
  have hcard' : Nat.card (monoHom (G := Ωˣ) A').ker = A'.det.natAbs := by
    simpa only [CFSG.HardMathSupport.Lang.TwE6Step3.monoHom_eq_monomialHom] using
      CFSG.RankThree.Classical2.natCard_ker_monomialHom (Ω := Ω) A' hA'
  let φ : (ι → Ωˣ) ≃* (Fin (Fintype.card ι) → Ωˣ) :=
    { toFun := fun c => c ∘ e.symm
      invFun := fun d => d ∘ e
      left_inv := fun c => by ext i; simp
      right_inv := fun d => by ext k; simp
      map_mul' := fun c d => by ext k; rfl }
  have hmap : ∀ c : ι → Ωˣ, monoHom A' (φ c) = φ (monoHom A c) := by
    intro c
    funext k
    show ∏ j : Fin (Fintype.card ι), c (e.symm j) ^ A (e.symm k) (e.symm j) =
      ∏ i : ι, c i ^ A (e.symm k) i
    exact Equiv.prod_comp e.symm (fun i => c i ^ A (e.symm k) i)
  have hker : (monoHom A).ker.map (φ : (ι → Ωˣ) →* (Fin (Fintype.card ι) → Ωˣ)) =
      (monoHom A').ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change monoHom A' (φ y) = 1
      rw [hmap, (MonoidHom.mem_ker).mp hy, map_one]
    · intro hx
      refine ⟨φ.symm x, ?_, by simp⟩
      change monoHom A (φ.symm x) = 1
      apply φ.injective
      rw [← hmap, MulEquiv.apply_symm_apply, (MonoidHom.mem_ker).mp hx, map_one]
  have hcard : Nat.card (monoHom (G := Ωˣ) A).ker =
      Nat.card (monoHom (G := Ωˣ) A').ker := by
    have h := Nat.card_congr (MulEquiv.subgroupMap φ (monoHom A).ker).toEquiv
    rwa [hker] at h
  rw [hcard, hcard', hA'det]

end Algebra

section Cyclotomic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem natCard_ker_monoHom_cyclotomic {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {P G : Matrix ι ι ℤ}
    (hP : P * P + P + 1 = 0) (hG : Pᵀ * G * P = G) (hdet : G.det ≠ 0) {q : ℕ}
    (hq : ((q : Ω) ^ 2 + q + 1) ≠ 0) :
    Nat.card (monoHom (G := Ωˣ) ((q : ℤ) • P - 1)).ker ^ 2 = (q ^ 2 + q + 1) ^ Fintype.card ι := by
  have hsq := det_smul_sub_one_sq hP hG hdet (q : ℤ)
  have hne : (((q : ℤ) • P - 1).det : Ω) ≠ 0 := by
    intro h0
    have h1 : ((((q : ℤ) • P - 1).det ^ 2 : ℤ) : Ω) = 0 := by
      rw [Int.cast_pow, h0]
      norm_num
    rw [hsq] at h1
    have h2 : (((q : ℤ) ^ 2 + q + 1 : ℤ) : Ω) ^ Fintype.card ι = 0 := by
      simpa using h1
    have h3 : (((q : ℤ) ^ 2 + q + 1 : ℤ) : Ω) = 0 := (pow_eq_zero_iff'.1 h2).1
    apply hq
    simpa using h3
  rw [natCard_ker_monoHom _ hne]
  have h3 : (((q : ℤ) • P - 1).det.natAbs : ℤ) ^ 2 = ((q ^ 2 + q + 1 : ℕ) : ℤ) ^ Fintype.card ι := by
    rw [Int.natAbs_sq, hsq]
    push_cast
    ring
  exact_mod_cast h3

theorem pow_eq_one_of_mem_ker_monoHom_cyclotomic {P : Matrix ι ι ℤ} (hP : P * P + P + 1 = 0)
    {G : Type*} [CommGroup G] (q : ℤ) {c : ι → G} (hc : monoHom (q • P - 1) c = 1) (i : ι) :
    c i ^ (q ^ 2 + q + 1) = 1 := by
  have hPP : P * P = -(P + 1) := eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
  have hP3 : P * P * P = 1 := by
    rw [hPP, neg_mul, add_mul, one_mul, hPP]
    abel
  refine pow_eq_one_of_mem_ker_monoHom (A := q • P - 1) (B := q • (P * P) - 1) ?_ hc i
  have e1 : (q • (P * P) - 1) * (q • P - 1) =
      (q ^ 2) • (P * P * P) - q • (P * P + P) + 1 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
    module
  rw [e1, hP3, hPP]
  module

end Cyclotomic

end CFSG.StandardType
