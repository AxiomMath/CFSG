module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.SimpleRing.Field

public section

open scoped TensorProduct

namespace CFSG

universe u v w

theorem finrank_le_finrank_of_injective_of_isFractionRing {A : Type u} (K : Type v) {M : Type w}
    {V : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (f : M →ₗ[A] V) (hf : Function.Injective f) : Module.finrank A M ≤ Module.finrank K V := by
  have hrank := LinearMap.lift_rank_le_of_injective f hf
  have hrank_eq : Module.rank A V = Module.rank K V :=
    (IsLocalization.rank_eq (R := A) (S := K) (N := V) (nonZeroDivisors A) le_rfl).symm
  have hfinK : Module.rank K V < Cardinal.aleph0 := Module.rank_lt_aleph0 K V
  have hfinA : Module.rank A V < Cardinal.aleph0 := by rwa [hrank_eq]
  have h := Module.finrank_le_finrank_of_rank_le_rank hrank hfinA
  calc Module.finrank A M ≤ Module.finrank A V := h
    _ = Module.finrank K V :=
      (IsLocalization.finrank_eq (R := A) (S := K) (N := V) (nonZeroDivisors A) le_rfl).symm

theorem exists_finrank_le_of_algHom (A : Type u) (P : Type v) [CommRing A] [IsDomain A]
    [CommRing P] [Algebra A P] [Algebra.FiniteType A P]
    (hinj : Function.Injective (algebraMap A P)) :
    ∃ d : ℕ, ∀ (B : Type w) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B],
      (B →ₐ[A] P) → Module.finrank A B ≤ d := by
  classical
  let K := FractionRing A
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  let P' := K ⊗[A] P
  have hP' : Nontrivial P' := by
    have h : Function.Injective (Algebra.TensorProduct.includeLeft :
        K →ₐ[A] K ⊗[A] P) :=
      Algebra.TensorProduct.includeLeft_injective (R := A) (A := K) (B := P) hinj
    have hne : (1 : P') ≠ 0 := fun h0 =>
      one_ne_zero (h (by rw [map_one, map_zero]; exact h0))
    exact nontrivial_of_ne 1 0 hne
  obtain ⟨m, hm⟩ := Ideal.exists_maximal P'
  have : m.IsMaximal := hm
  let V := P' ⧸ m
  let : Field V := Ideal.Quotient.field m
  have : Algebra.FiniteType K P' := Algebra.FiniteType.baseChange (R := A) (A := P) K
  have : Algebra.FiniteType K V := Algebra.FiniteType.quotient K m
  have : IsJacobsonRing K := inferInstance
  have : Module.Finite K V := finite_of_finite_type_of_isJacobsonRing K V
  refine ⟨Module.finrank K V, ?_⟩
  intro B _ _ _ _ φ
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let q : P' →ₐ[A] V := Ideal.Quotient.mkₐ A m
  let ψ : B →ₐ[A] V := q.comp ((Algebra.TensorProduct.includeRight :
      P →ₐ[A] P').comp φ)
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : IsSimpleRing K := (isSimpleRing_iff_isField K).2 (Field.toIsField K)
  have hKV : Function.Injective (algebraMap K V) := RingHom.injective (algebraMap K V)
  have hAV : Function.Injective (algebraMap A V) := by
    rw [IsScalarTower.algebraMap_eq A K V]
    exact hKV.comp hAK
  have hcomap : Ideal.under A (RingHom.ker ψ) = ⊥ := by
    ext a
    rw [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => hAV (by rw [map_zero]; exact h), fun h => by rw [h, map_zero]⟩
  have hψ : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    exact Ideal.eq_bot_of_comap_eq_bot (R := A) (S := B) (I := RingHom.ker ψ) hcomap
  exact finrank_le_finrank_of_injective_of_isFractionRing K ψ.toLinearMap hψ

theorem finrank_tensorProduct_eq_finrank_of_flat
    {A B L : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Flat A B] [Field L] [Algebra A L] :
    Module.finrank L (TensorProduct A L B) = Module.finrank A B := by
  let p : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  have hfree : Module.Free L (TensorProduct A L B) := Module.Free.of_divisionRing L _
  have h1 : Module.rankAtStalk (TensorProduct A L B) p
      = Module.finrank L (TensorProduct A L B) := by
    simp
  rw [← h1, Module.rankAtStalk_baseChange]
  have hker : PrimeSpectrum.comap (algebraMap A L) p
      = ⟨RingHom.ker (algebraMap A L), RingHom.ker_isPrime (algebraMap A L)⟩ := rfl
  rw [hker]
  have hprime : (RingHom.ker (algebraMap A L)).IsPrime :=
    RingHom.ker_isPrime (algebraMap A L)
  rw [← Ideal.finrank_fiber_eq_rankAtStalk (M := B)
    (p := RingHom.ker (algebraMap A L))]
  exact Ideal.finrank_fiber_eq_finrank (M := B) (p := RingHom.ker (algebraMap A L))

theorem finrank_quotient_map_eq_mul (k : Type u) {A : Type v} {B : Type w} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.Finite A B] [Module.Flat A B] (I : Ideal A) [Module.Finite k (A ⧸ I)] :
    Module.finrank k (B ⧸ I.map (algebraMap A B)) = Module.finrank k (A ⧸ I) * Module.finrank A B := by
  let C := A ⧸ I
  have hCfinite : Module.Finite k C := ‹Module.Finite k (A ⧸ I)›
  have hCMfinite : Module.Finite C (TensorProduct A C B) := Module.Finite.base_change A C B
  have hCMflat : Module.Flat C (TensorProduct A C B) := Module.Flat.baseChange A C B
  have hCartin : IsArtinianRing C := IsArtinianRing.of_finite k C
  have hCmax : Finite (MaximalSpectrum C) := IsArtinianRing.instFiniteMaximalSpectrum C
  let hfield : ∀ P : MaximalSpectrum C, Field (C ⧸ P.asIdeal) :=
    fun P => Ideal.Quotient.field P.asIdeal
  have hrank : ∀ P : MaximalSpectrum C,
      Module.finrank (C ⧸ P.asIdeal)
        ((C ⧸ P.asIdeal) ⊗[C] (TensorProduct A C B)) = Module.finrank A B := by
    intro P
    let K := C ⧸ P.asIdeal
    let L := P.asIdeal.ResidueField
    have hbase : Module.finrank L (TensorProduct K L (TensorProduct C K (TensorProduct A C B)))
        = Module.finrank K (TensorProduct C K (TensorProduct A C B)) :=
      Module.finrank_baseChange (R := L) (S := K)
        (M' := TensorProduct C K (TensorProduct A C B))
    rw [← hbase]
    let e1 : TensorProduct K L (TensorProduct C K (TensorProduct A C B)) ≃ₗ[L]
        TensorProduct C L (TensorProduct A C B) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange C K L L (TensorProduct A C B)
    let e2 : TensorProduct C L (TensorProduct A C B) ≃ₗ[L] TensorProduct A L B :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A C L L B
    rw [e1.finrank_eq, e2.finrank_eq]
    exact finrank_tensorProduct_eq_finrank_of_flat (A := A) (B := B) (L := L)
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq C (TensorProduct A C B)
    (Module.finrank A B) hrank
  let n := Module.finrank A B
  have hb : TensorProduct A C B ≃ₗ[C] (Fin n → C) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite C C (Fin n))
  have hbK : TensorProduct A C B ≃ₗ[k] (Fin n → C) := hb.restrictScalars k
  have hfin : Module.finrank k (TensorProduct A C B) = n * Module.finrank k C := by
    rw [hbK.finrank_eq, Module.finrank_pi_fintype]
    simp [Finset.sum_const]
  have e : (B ⧸ I.map (algebraMap A B)) ≃ₗ[k] TensorProduct A C B :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.restrictScalars k).trans
      ((TensorProduct.comm A B C).restrictScalars k)
  calc
    Module.finrank k (B ⧸ I.map (algebraMap A B))
        = Module.finrank k (TensorProduct A C B) := e.finrank_eq
    _ = n * Module.finrank k C := hfin
    _ = Module.finrank k C * n := by rw [mul_comm]
    _ = Module.finrank k (A ⧸ I) * Module.finrank A B := rfl

theorem moduleFinite_quotient_map (k : Type u) {A : Type v} {B : Type w} [Field k] [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.Finite A B] (I : Ideal A) [Module.Finite k (A ⧸ I)] :
    Module.Finite k (B ⧸ I.map (algebraMap A B)) := by
  have : Module.Finite (A ⧸ I) ((A ⧸ I) ⊗[A] B) := Module.Finite.base_change A (A ⧸ I) B
  have : Module.Finite k ((A ⧸ I) ⊗[A] B) := Module.Finite.trans (A ⧸ I) ((A ⧸ I) ⊗[A] B)
  exact Module.Finite.equiv
    (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.restrictScalars k).trans
      ((TensorProduct.comm A B (A ⧸ I)).restrictScalars k)).symm

end CFSG
