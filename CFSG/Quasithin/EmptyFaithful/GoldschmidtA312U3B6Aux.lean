module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.Quasithin.A312U3

open Subgroup Matrix

theorem card_ringEquiv_eq {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) : Nat.card (K ≃+* K) = f := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hKF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃ (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (by
        intro x
        have h : (σ.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
            algebraMap (ZMod p) K := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun σ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl }
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank]
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := K)
  rw [hK, Nat.card_zmod] at h1
  exact (Nat.pow_right_injective hp.two_le h1).symm

theorem eq_of_ne_one_of_card_le_two' {A : Type*} [Group A] [Finite A] (hA : Nat.card A ≤ 2)
    {x y : A} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  let _ : Fintype A := Fintype.ofFinite A
  have hsub : ({1, x, y} : Finset A).card ≤ Fintype.card A := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem, Finset.card_pair hxy] at hsub
  · rw [← Nat.card_eq_fintype_card] at hsub
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx, Ne.symm hy⟩

theorem exists_conj_pow_of_orderOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ^ 2 ∣ Nat.card G) {x y : G} (hx : orderOf x = p) (hy : orderOf y = p) :
    ∃ (g : G) (k : ℕ), g * y * g⁻¹ = x ^ k := by
  classical
  have hdvd : p ∣ Nat.card G := hx ▸ orderOf_dvd_natCard x
  have hfac : (Nat.card G).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card G).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').1 (by simpa using hdvd)
    have h2 : ¬ 2 ≤ (Nat.card G).factorization p := fun h =>
      hp ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').2 h)
    omega
  have hpg : ∀ z : G, orderOf z = p → IsPGroup p (zpowers z) := fun z hz => by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  obtain ⟨Px, hPx⟩ := (hpg x hx).exists_le_sylow
  obtain ⟨Py, hPy⟩ := (hpg y hy).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Py Px
  have hcard : Nat.card (Px : Subgroup G) = p := by
    rw [Px.card_eq_multiplicity, hfac, pow_one]
  have hxeq : (Px : Subgroup G) = zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hPx ?_
    rw [hcard, Nat.card_zpowers, hx]
  have hmem : g * y * g⁻¹ ∈ (Px : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨y, hPy (mem_zpowers y), by simp [MulAut.conj_apply]⟩
  rw [hxeq, mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hmem
  obtain ⟨k, -, hk⟩ := hmem
  exact ⟨g, k, hk.symm⟩

section Trace

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_conj_gl (A : GL n R) (M : Matrix n n R) :
    Matrix.trace ((A : Matrix n n R) * M * ((A⁻¹ : GL n R) : Matrix n n R)) =
      Matrix.trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem det_conj_gl (A : GL n R) (M : Matrix n n R) :
    Matrix.det ((A : Matrix n n R) * M * ((A⁻¹ : GL n R) : Matrix n n R)) = Matrix.det M := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Units.mul_inv,
    Matrix.det_one, one_mul]

end Trace

end CFSG.Quasithin.A312U3
