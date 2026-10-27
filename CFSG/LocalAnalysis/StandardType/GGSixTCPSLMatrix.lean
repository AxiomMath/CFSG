module

public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.StandardType.TableCRes

section AuxAll

open CFSG.StandardType.ClassicalPosition Matrix

section Aux

variable {F K : Type} [Field F] [Finite F] [Field K] [Algebra F K] [Finite K]

theorem card_le_of_matrix_algebra {N p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (φ : K →ₐ[F] Matrix (Fin N) (Fin N) F) {ι : Type} [Finite ι] (g : ι → GL (Fin N) F)
    (hgcomm : ∀ i j, g i * g j = g j * g i)
    (hgφ : ∀ i (c : K), (g i : Matrix (Fin N) (Fin N) F) * φ c =
      φ c * (g i : Matrix (Fin N) (Fin N) F))
    (hgpow : ∀ i, ∃ w : Fˣ, g i ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) w)
    (hginj : ∀ i j (w : Fˣ), g i = g j * Matrix.GeneralLinearGroup.scalar (Fin N) w → i = j) :
    ∃ n, Module.finrank F K * n = N ∧ Nat.card ι ≤ p ^ n := by
  classical
  let V := Fin N → F
  let κ : K →ₐ[F] Module.End F V :=
    (Matrix.toLinAlgEquiv' :
      Matrix (Fin N) (Fin N) F ≃ₐ[F] Module.End F (Fin N → F)).toAlgHom.comp φ
  let instK : Module K V := Module.compHom V (κ : K →+* Module.End F V)
  have hsmul : ∀ (c : K) (v : V), c • v = κ c v := fun _ _ => rfl
  have hκ_apply : ∀ (c : K) (v : V), κ c v = (φ c) *ᵥ v := fun c v => rfl
  have : IsScalarTower F K V := ⟨fun r c v => by
    rw [hsmul (r • c) v, hsmul c v, map_smul]
    rfl⟩
  have : FiniteDimensional K V := Module.Finite.of_restrictScalars_finite F K V
  let ρ : GL (Fin N) F →* (V ≃ₗ[F] V) :=
    ((Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := F)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F V)).toMonoidHom
  have hρ : ∀ (s : GL (Fin N) F) (v : V), ρ s v = (s : Matrix (Fin N) (Fin N) F) *ᵥ v := by
    intro s v
    exact Matrix.GeneralLinearGroup.toLin_apply s v
  have hρinj : Function.Injective ρ :=
    ((Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := F)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F V)).injective
  have hρscal : ∀ w : Fˣ, ρ (Matrix.GeneralLinearGroup.scalar (Fin N) w) = scalarEquiv F V w := by
    intro w
    ext v
    rw [hρ, scalarEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar]
    simp [Matrix.scalar_apply]
    rfl
  have key := card_le_pow_finrank (F := F) (K := K) (V := V) hp hpK (fun i => ρ (g i))
    (fun i j => by rw [← map_mul, ← map_mul, hgcomm])
    (fun i c v => by
      rw [hρ, hρ, hsmul, hκ_apply, hsmul, hκ_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rw [hgφ i c])
    (fun i => by
      obtain ⟨w, hw⟩ := hgpow i
      exact ⟨w, by rw [← map_pow, hw, hρscal]⟩)
    (fun i j w h => hginj i j w (hρinj (by rw [map_mul, hρscal]; exact h)))
  refine ⟨Module.finrank K V, ?_, key⟩
  have h1 := Module.finrank_mul_finrank F K V
  rw [Module.finrank_fin_fun] at h1
  exact h1

end Aux

end AuxAll

section Aux2All

open CFSG.StandardType.ClassicalPosition Polynomial

section Aux2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_le_of_nonpow_matrix {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : GL (Fin N) F) (u : Fˣ) (ha : a ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) u)
    (hu : ∀ μ : F, μ ^ p ≠ (u : F)) {ι : Type} [Finite ι] (g : ι → GL (Fin N) F)
    (hgcomm : ∀ i j, g i * g j = g j * g i) (hga : ∀ i, g i * a = a * g i)
    (hgpow : ∀ i, ∃ w : Fˣ, g i ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) w)
    (hginj : ∀ i j (w : Fˣ), g i = g j * Matrix.GeneralLinearGroup.scalar (Fin N) w → i = j) :
    ∃ n, N = p * n ∧ Nat.card ι ≤ p ^ n := by
  classical
  have hirr : Irreducible (X ^ p - C (u : F)) := X_pow_sub_C_irreducible_of_prime hp hu
  have : Fact (Irreducible (X ^ p - C (u : F))) := ⟨hirr⟩
  have hne : (X ^ p - C (u : F)) ≠ 0 := hirr.ne_zero
  have : Module.Finite F (AdjoinRoot (X ^ p - C (u : F))) := (AdjoinRoot.powerBasis hne).finite
  have : Finite (AdjoinRoot (X ^ p - C (u : F))) := Module.finite_of_finite F
  have hroot : aeval (a : Matrix (Fin N) (Fin N) F) (X ^ p - C (u : F)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    have h1 : ((a ^ p : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) =
        (a : Matrix (Fin N) (Fin N) F) ^ p := Units.val_pow_eq_pow_val _ _
    rw [ha, Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [← h1, Algebra.algebraMap_eq_smul_one]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  let φ : AdjoinRoot (X ^ p - C (u : F)) →ₐ[F] Matrix (Fin N) (Fin N) F :=
    Ideal.Quotient.liftₐ (Ideal.span {X ^ p - C (u : F)})
      (aeval (a : Matrix (Fin N) (Fin N) F)) (fun P hP => by
        obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hP
        rw [map_mul, hroot, zero_mul])
  have hpF : (p : F) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff F 2] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hpK : ((p : ℕ) : AdjoinRoot (X ^ p - C (u : F))) ≠ 0 := by
    intro h
    apply hpF
    apply (algebraMap F (AdjoinRoot (X ^ p - C (u : F)))).injective
    rw [map_natCast, map_zero]
    exact h
  have hgφ : ∀ i (c : AdjoinRoot (X ^ p - C (u : F))),
      (g i : Matrix (Fin N) (Fin N) F) * φ c = φ c * (g i : Matrix (Fin N) (Fin N) F) := by
    intro i c
    induction c using AdjoinRoot.induction_on with
    | ih P =>
      have hφP : φ (AdjoinRoot.mk _ P) = aeval (a : Matrix (Fin N) (Fin N) F) P := by
        exact Ideal.Quotient.liftₐ_apply _ _ _ _
      rw [hφP]
      have hcomm : (g i : Matrix (Fin N) (Fin N) F) * (a : Matrix (Fin N) (Fin N) F) =
          (a : Matrix (Fin N) (Fin N) F) * (g i : Matrix (Fin N) (Fin N) F) :=
        congrArg Units.val (hga i)
      have hle : Algebra.adjoin F
          ({(a : Matrix (Fin N) (Fin N) F)} : Set (Matrix (Fin N) (Fin N) F)) ≤
          Subalgebra.centralizer F
            ({(g i : Matrix (Fin N) (Fin N) F)} : Set (Matrix (Fin N) (Fin N) F)) := by
        apply Algebra.adjoin_le
        rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hcomm
      have hmem := hle (P.aeval_mem_adjoin_singleton F (a : Matrix (Fin N) (Fin N) F))
      rw [Subalgebra.mem_centralizer_iff] at hmem
      exact hmem _ rfl
  obtain ⟨n, hn, hcard⟩ := card_le_of_matrix_algebra hp hpK φ g hgcomm hgφ hgpow hginj
  have hdeg : Module.finrank F (AdjoinRoot (X ^ p - C (u : F))) = p := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  rw [hdeg] at hn
  exact ⟨n, hn.symm, hcard⟩

end Aux2

end Aux2All

end CFSG.StandardType.TableCRes
