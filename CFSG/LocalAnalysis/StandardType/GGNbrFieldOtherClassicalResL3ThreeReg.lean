module

public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.StandardType.L3Three

open Matrix Polynomial

variable {F : Type*} [Field F]

@[expose] def krylov (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i j => (B ^ (j : ℕ) *ᵥ v) i

theorem krylov_apply (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) (i j : Fin 3) :
    krylov B v i j = (B ^ (j : ℕ) *ᵥ v) i :=
  rfl

@[expose] def IsReg (B : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ v : Fin 3 → F, (krylov B v).det ≠ 0

theorem krylov_mulVec (B : Matrix (Fin 3) (Fin 3) F) (v c : Fin 3 → F) :
    krylov B v *ᵥ c = (∑ j : Fin 3, c j • B ^ (j : ℕ)) *ᵥ v := by
  ext i
  simp only [Fin.sum_univ_three, mulVec, dotProduct, krylov_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem mul_krylov {B M : Matrix (Fin 3) (Fin 3) F} (hM : Commute M B) (v : Fin 3 → F) :
    M * krylov B v = krylov B (M *ᵥ v) := by
  ext i j
  have h1 : (M * krylov B v) i j = (M *ᵥ (B ^ (j : ℕ) *ᵥ v)) i := by
    simp only [mul_apply, krylov_apply, mulVec, dotProduct]
  rw [h1, krylov_apply, mulVec_mulVec, mulVec_mulVec, ((hM.pow_right (j : ℕ)).eq)]

theorem IsReg.eq_sum_pow {B M : Matrix (Fin 3) (Fin 3) F} (hB : IsReg B) (hM : Commute M B) :
    ∃ c : Fin 3 → F, M = ∑ j : Fin 3, c j • B ^ (j : ℕ) := by
  obtain ⟨v, hv⟩ := hB
  set Q := krylov B v with hQ
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hv
  set c : Fin 3 → F := Q⁻¹ *ᵥ (M *ᵥ v) with hc
  refine ⟨c, ?_⟩
  set P : Matrix (Fin 3) (Fin 3) F := ∑ j : Fin 3, c j • B ^ (j : ℕ) with hP
  have hPB : Commute P B := by
    rw [hP]
    refine Commute.sum_left _ _ _ fun j _ => ?_
    exact (Commute.pow_left (Commute.refl B) _).smul_left _
  have hPv : P *ᵥ v = M *ᵥ v := by
    rw [hP, ← krylov_mulVec, ← hQ, hc, mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
  have hMQ : M * Q = P * Q := by
    rw [hQ, mul_krylov hM, mul_krylov hPB, hPv]
  calc M = M * Q * Q⁻¹ := by rw [mul_assoc, mul_nonsing_inv _ hQu, mul_one]
    _ = P * Q * Q⁻¹ := by rw [hMQ]
    _ = P := by rw [mul_assoc, mul_nonsing_inv _ hQu, mul_one]

theorem IsReg.commute {B M N : Matrix (Fin 3) (Fin 3) F} (hB : IsReg B) (hM : Commute M B)
    (hN : Commute N B) : Commute M N := by
  obtain ⟨c, rfl⟩ := hB.eq_sum_pow hM
  obtain ⟨d, rfl⟩ := hB.eq_sum_pow hN
  refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_
  exact ((Commute.pow_pow_self B _ _).smul_left _).smul_right _

theorem IsReg.map {F' : Type*} [Field F'] (f : F →+* F') {B : Matrix (Fin 3) (Fin 3) F}
    (hB : IsReg B) : IsReg (B.map f) := by
  obtain ⟨v, hv⟩ := hB
  refine ⟨f ∘ v, ?_⟩
  have hk : krylov (B.map f) (f ∘ v) = (krylov B v).map f := by
    ext i j
    rw [krylov_apply, map_apply, krylov_apply, RingHom.map_mulVec, ← RingHom.mapMatrix_apply,
      ← map_pow, RingHom.mapMatrix_apply]
  rw [hk, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero f).mpr hv

theorem IsReg.conj {B : Matrix (Fin 3) (Fin 3) F} (hB : IsReg B) (P : GL (Fin 3) F) :
    IsReg ((P : Matrix (Fin 3) (Fin 3) F) * B *
      ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  obtain ⟨v, hv⟩ := hB
  refine ⟨(P : Matrix (Fin 3) (Fin 3) F) *ᵥ v, ?_⟩
  have hk : krylov ((P : Matrix (Fin 3) (Fin 3) F) * B *
      ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      (P : Matrix (Fin 3) (Fin 3) F) * krylov B v := by
    ext i j
    have h1 : ((P : Matrix (Fin 3) (Fin 3) F) * krylov B v) i j =
        ((P : Matrix (Fin 3) (Fin 3) F) *ᵥ (B ^ (j : ℕ) *ᵥ v)) i := by
      simp only [mul_apply, krylov_apply, mulVec, dotProduct]
    rw [h1, krylov_apply, Units.conj_pow, mulVec_mulVec, mulVec_mulVec,
      mul_assoc ((P : Matrix (Fin 3) (Fin 3) F) * B ^ (j : ℕ)), Units.inv_mul, mul_one]
  rw [hk, det_mul]
  exact mul_ne_zero (P.isUnit.map (detMonoidHom (n := Fin 3) (R := F))).ne_zero hv

theorem IsReg.smul {B : Matrix (Fin 3) (Fin 3) F} (hB : IsReg B) {c : F} (hc : c ≠ 0) :
    IsReg (c • B) := by
  obtain ⟨v, hv⟩ := hB
  refine ⟨v, ?_⟩
  have hk : krylov (c • B) v = krylov B v * diagonal fun j : Fin 3 => c ^ (j : ℕ) := by
    ext i j
    rw [mul_diagonal, krylov_apply, krylov_apply, smul_pow, smul_mulVec, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  rw [hk, det_mul, det_diagonal]
  refine mul_ne_zero hv ?_
  exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ hc

theorem isReg_diagonal {s : Fin 3 → F} (hs : Function.Injective s) : IsReg (diagonal s) := by
  refine ⟨fun _ => 1, ?_⟩
  have hk : krylov (diagonal s) (fun _ => 1) = vandermonde s := by
    ext i j
    rw [krylov_apply, vandermonde_apply, diagonal_pow, mulVec_diagonal, mul_one]
    rfl
  rw [hk]
  exact det_vandermonde_ne_zero_iff.mpr hs

theorem isReg_of_pow_three_eq {B : Matrix (Fin 3) (Fin 3) F} {l : F}
    (hB : B ^ 3 = scalar (Fin 3) l) (hl : ∀ c : F, c ^ 3 ≠ l) : IsReg B := by
  refine ⟨Pi.single 0 1, fun h0 => ?_⟩
  obtain ⟨c, hc0, hc⟩ := exists_mulVec_eq_zero_iff.mpr h0
  set p : F[X] := C (c 0) + C (c 1) * X + C (c 2) * X ^ 2 with hp
  set q : F[X] := X ^ 3 - C l with hq
  have hqdeg : q.natDegree = 3 := by
    rw [hq]
    exact natDegree_X_pow_sub_C
  have hqirr : Irreducible q := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hqdeg]; decide) fun x hx => ?_
    rw [hq, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hx
    exact hl x hx
  have hpdeg : p.natDegree ≤ 2 := by
    rw [hp]
    compute_degree
  have hp0 : p ≠ 0 := by
    intro hp0
    apply hc0
    have h0 : p.coeff 0 = c 0 := by rw [hp]; simp
    have h1 : p.coeff 1 = c 1 := by rw [hp]; simp
    have h2 : p.coeff 2 = c 2 := by rw [hp]; simp
    rw [hp0, coeff_zero] at h0 h1 h2
    ext j
    fin_cases j
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
  have hndvd : ¬ q ∣ p := by
    intro hdvd
    have := natDegree_le_of_dvd hdvd hp0
    omega
  obtain ⟨a, b, hab⟩ := (hqirr.coprime_iff_not_dvd).mpr hndvd
  have hqB : aeval B q = 0 := by
    rw [hq, map_sub, map_pow, aeval_X, aeval_C, hB, algebraMap_eq_diagonal]
    rw [sub_eq_zero]
    rfl
  have hpB : aeval B p = ∑ j : Fin 3, c j • B ^ (j : ℕ) := by
    rw [hp, Fin.sum_univ_three]
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, algebraMap_smul, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, Algebra.smul_def, mul_one]
  have hpv : aeval B p *ᵥ (Pi.single 0 1 : Fin 3 → F) = 0 := by
    rw [hpB, ← krylov_mulVec, hc]
  have h1 := congrArg (aeval B) hab
  rw [map_add, map_mul, map_mul, hqB, mul_zero, zero_add, map_one] at h1
  have h2 : (Pi.single 0 1 : Fin 3 → F) = 0 := by
    calc (Pi.single 0 1 : Fin 3 → F) = (aeval B b * aeval B p) *ᵥ Pi.single 0 1 := by
          rw [h1, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hpv, mulVec_zero]
  have h3 := congrFun h2 0
  simp at h3

end CFSG.StandardType.L3Three

end
