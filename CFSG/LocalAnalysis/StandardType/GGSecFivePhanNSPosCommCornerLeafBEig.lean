module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Pi
import CFSG.LinearAlgebra.MatrixPlanes
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLift
import CFSG.RankThree.PartOne.CTP.SeitzDiag
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep

public section

namespace CFSG.StandardType

open Matrix

open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

private lemma ggNSPosPF3C_mat2_sq_trace_sub_det (A : Matrix (Fin 2) (Fin 2) K) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private lemma ggNSPosPF3C_mat2_sq_trace_add_det (A : Matrix (Fin 2) (Fin 2) K) :
    A * A = A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h := ggNSPosPF3C_mat2_sq_trace_sub_det A
  rwa [CharTwo.sub_eq_add] at h

private lemma ggNSPosPF3C_mat2_cube_of_CH {A : Matrix (Fin 2) (Fin 2) K}
    (hCH : A * A = A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) K)) :
    A ^ 3 = (A.trace ^ 2 + A.det) • A + (A.trace * A.det) • 1 := by
  calc A ^ 3 = A * (A * A) := by rw [pow_three]
    _ = A * (A.trace • A + A.det • 1) := by rw [hCH]
    _ = A.trace • (A * A) + A.det • A := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    _ = A.trace • (A.trace • A + A.det • 1) + A.det • A := by rw [hCH]
    _ = (A.trace ^ 2 + A.det) • A + (A.trace * A.det) • 1 := by
          rw [smul_add, smul_smul, smul_smul, add_assoc,
            add_comm ((A.trace * A.det) • 1) (A.det • A), ← add_assoc, ← add_smul, ← pow_two]

private lemma ggNSPosPF3C_mat2_quadratic {A : Matrix (Fin 2) (Fin 2) K} {s : K}
    (hA3 : A ^ 3 = s • (1 : Matrix (Fin 2) (Fin 2) K))
    (hns : ¬ ∃ a : K, A = a • (1 : Matrix (Fin 2) (Fin 2) K)) :
    A * A = A.trace • A + A.trace ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hCH : A * A = A.trace • A + A.det • 1 := ggNSPosPF3C_mat2_sq_trace_add_det A
  have hcube : (A.trace ^ 2 + A.det) • A = (s + A.trace * A.det) • 1 := by
    have h1 : (A.trace ^ 2 + A.det) • A + (A.trace * A.det) • 1 = s • 1 := by
      rw [← ggNSPosPF3C_mat2_cube_of_CH hCH, hA3]
    have h2 := congrArg (fun Z => Z + (A.trace * A.det) • 1) h1
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, ← add_smul] at h2
    exact h2
  by_cases h : A.trace ^ 2 + A.det = 0
  · have hdet : A.det = A.trace ^ 2 := by
      have h' : A.trace ^ 2 = -A.det := (add_eq_zero_iff_eq_neg.mp h)
      rw [h', CharTwo.neg_eq]
    rw [hCH, hdet]
  · exfalso
    apply hns
    refine ⟨(s + A.trace * A.det) * (A.trace ^ 2 + A.det)⁻¹, ?_⟩
    calc A = 1 • A := (one_smul K A).symm
      _ = ((A.trace ^ 2 + A.det)⁻¹ * (A.trace ^ 2 + A.det)) • A := by
            rw [inv_mul_cancel₀ h, one_smul]
      _ = (A.trace ^ 2 + A.det)⁻¹ • ((A.trace ^ 2 + A.det) • A) := by rw [smul_smul]
      _ = (A.trace ^ 2 + A.det)⁻¹ • ((s + A.trace * A.det) • 1) := by rw [hcube]
      _ = ((A.trace ^ 2 + A.det)⁻¹ * (s + A.trace * A.det)) • 1 := by rw [smul_smul]
      _ = ((s + A.trace * A.det) * (A.trace ^ 2 + A.det)⁻¹) • 1 := by rw [mul_comm]

private lemma ggNSPosPF3C_mulVec_eq_zero_of_commute {p : ℕ} (hp : p.Prime)
    {X Y : GL (Fin n) K} {z : Kˣ} (hz : IsPrimitiveRoot (z : K) p) (hX : X ^ p = 1)
    (hXY : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X)
    (Z : Matrix (Fin n) (Fin n) K)
    (hZY : Z * (Y : Matrix (Fin n) (Fin n) K) =
      (Y : Matrix (Fin n) (Fin n) K) * Z)
    (hZ0 : ∀ v ∈ Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1,
      Z *ᵥ v = 0)
    (v : Fin n → K) : Z *ᵥ v = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)
      (Matrix.GeneralLinearGroup.toLin X) with hg
  have hgL : g.toLinearMap = Matrix.toLin' (X : Matrix (Fin n) (Fin n) K) := by
    rw [hg, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply']
  have hgp : g ^ p = 1 := by
    rw [hg, ← map_pow, ← map_pow, hX]
    simp
  have hdir : DirectSum.IsInternal (fun i : Fin p =>
      Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K))
        ((z : K) ^ (i : ℤ))) := by
    have h := CFSG.proposition_2_4_a (g := g) hgp hp.two_le (ε := (z : K)) hz
    simpa only [hgL] using h
  set L : Submodule K (Fin n → K) := LinearMap.ker (Matrix.toLin' Z) with hL
  have hmemL : ∀ w, w ∈ L ↔ Z *ᵥ w = 0 := fun w => by
    rw [hL, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hle : ∀ i : Fin p, Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K))
      ((z : K) ^ (i : ℤ)) ≤ L := by
    intro i
    have hk : (((z ^ (p - i.val) : Kˣ) : K))⁻¹ * 1 = (z : K) ^ (i : ℤ) := by
      rw [mul_one, zpow_natCast, Units.val_pow_eq_pow_val]
      have h1 : (z : K) ^ i.val * (z : K) ^ (p - i.val) = 1 := by
        rw [← pow_add, Nat.add_sub_cancel' i.isLt.le, hz.pow_eq_one]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rw [← hk, ← CFSG.LinearAlgebra.map_eigenspace_eq
      (CFSG.LinearAlgebra.pow_conj_eq_scalar hXY (p - i.val)) 1]
    rintro _ ⟨w, hw, rfl⟩
    rw [hmemL]
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    have hcomm : Z * ((Y ^ (p - i.val) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((Y ^ (p - i.val) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z := by
      rw [Units.val_pow_eq_pow_val]
      exact (show Commute Z ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) from hZY).pow_right _
        |>.eq
    rw [hcomm, ← Matrix.mulVec_mulVec, hZ0 w hw, Matrix.mulVec_zero]
  have htop : (⊤ : Submodule K (Fin n → K)) ≤ L :=
    hdir.submodule_iSup_eq_top ▸ iSup_le hle
  exact (hmemL v).1 (htop Submodule.mem_top)

theorem ggNSPosPF3C_quadratic_of_commutant {ω : K} (hω : IsPrimitiveRoot ω 3)
    {X Y N : GL (Fin n) K} (hX3 : X ^ 3 = 1)
    (hYX : (Y : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) =
      ω • ((X : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K)))
    (hNX : (N : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) =
      (X : Matrix (Fin n) (Fin n) K) * (N : Matrix (Fin n) (Fin n) K))
    (hNY : (N : Matrix (Fin n) (Fin n) K) * (Y : Matrix (Fin n) (Fin n) K) =
      (Y : Matrix (Fin n) (Fin n) K) * (N : Matrix (Fin n) (Fin n) K))
    (hN3 : ∃ s : K, ((N ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = s • 1)
    (hNns : ¬ ∃ s : K, (N : Matrix (Fin n) (Fin n) K) = s • 1)
    (hdim : Module.finrank K
      (Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1) = 2) :
    ∃ τ : K, τ ≠ 0 ∧ (N : Matrix (Fin n) (Fin n) K) * (N : Matrix (Fin n) (Fin n) K) =
      τ • (N : Matrix (Fin n) (Fin n) K) + τ ^ 2 • 1 := by
  set Xm : Matrix (Fin n) (Fin n) K := (X : Matrix (Fin n) (Fin n) K) with hXm
  set Ym : Matrix (Fin n) (Fin n) K := (Y : Matrix (Fin n) (Fin n) K) with hYm
  set Nm : Matrix (Fin n) (Fin n) K := (N : Matrix (Fin n) (Fin n) K) with hNm
  have hNXm : Nm * Xm = Xm * Nm := hNX
  have hNYm : Nm * Ym = Ym * Nm := hNY
  have hn : Nonempty (Fin n) := by
    by_contra h
    apply hNns
    refine ⟨0, ?_⟩
    ext i j
    exact (h ⟨i⟩).elim
  haveI := hn
  obtain ⟨s, hs⟩ := hN3
  have hNcube : Nm ^ 3 = s • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hNm, ← Units.val_pow_eq_pow_val]
    exact hs
  set z : Kˣ := Units.mk0 ω (hω.ne_zero (by decide)) with hz
  have hzval : (z : K) = ω := by rw [hz]; rfl
  have hzprim : IsPrimitiveRoot (z : K) 3 := by rw [hzval]; exact hω
  have hYXgl : Y * X * Y⁻¹ = GeneralLinearGroup.scalar (Fin n) z * X := by
    apply Units.ext
    change (Y : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) *
        ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.scalar (Fin n) (z : K) * (X : Matrix (Fin n) (Fin n) K)
    have h1 : (Y : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K) *
        ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ω • (X : Matrix (Fin n) (Fin n) K) := by
      rw [hYX, Matrix.smul_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.mul_one]
    rw [h1, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, hzval]
  set V1 : Submodule K (Fin n → K) :=
    Module.End.eigenspace (Matrix.toLin' (X : Matrix (Fin n) (Fin n) K)) 1 with hV1
  have hdimV : Module.finrank K V1 = 2 := by rw [hV1]; exact hdim
  have hinv : ∀ v ∈ V1, Matrix.toLin' Nm v ∈ V1 := by
    intro v hv
    rw [hV1] at hv ⊢
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    simp only [Matrix.toLin'_apply, one_smul] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hNXm, ← Matrix.mulVec_mulVec, hv]
  set M : V1 →ₗ[K] V1 := (Matrix.toLin' Nm).restrict hinv with hM
  have hM_apply : ∀ v : V1, (M v : Fin n → K) = Nm *ᵥ (v : Fin n → K) := by
    intro v
    rw [hM, LinearMap.coe_restrict_apply, Matrix.toLin'_apply]
  have hM_apply_pow : ∀ (k : ℕ) (v : V1),
      ((M ^ k) v : Fin n → K) = (Nm ^ k) *ᵥ (v : Fin n → K) := by
    intro k
    induction k with
    | zero =>
        intro v
        simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
    | succ k ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, hM_apply, pow_succ, Matrix.mulVec_mulVec]
  have hM3 : M ^ 3 = s • (1 : V1 →ₗ[K] V1) := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [hM_apply_pow, hNcube]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, LinearMap.smul_apply,
      Module.End.one_apply, Submodule.coe_smul]
  set b : Module.Basis (Fin 2) K V1 := Module.finBasisOfFinrankEq K V1 hdimV with hb
  set A : Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrix b b M with hA
  have hA3 : A ^ 3 = s • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hA, LinearMap.toMatrix_pow, hM3]
    rw [map_smul, LinearMap.toMatrix_one]
  have hMns : ¬ ∃ a : K, M = a • (1 : V1 →ₗ[K] V1) := by
    rintro ⟨a, ha⟩
    apply hNns
    have hZ0 : ∀ v ∈ V1, (Nm - a • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ v = 0 := by
      intro v hv
      have hv' : (M ⟨v, hv⟩ : Fin n → K) = a • v := by
        rw [ha]
        simp only [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul,
          Subtype.coe_mk]
      rw [hM_apply] at hv'
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv', sub_self]
    have hZY : (Nm - a • (1 : Matrix (Fin n) (Fin n) K)) * Ym =
        Ym * (Nm - a • (1 : Matrix (Fin n) (Fin n) K)) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hNYm]
    have hZall : ∀ v, (Nm - a • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ v = 0 :=
      fun v => ggNSPosPF3C_mulVec_eq_zero_of_commute (p := 3) (by decide) hzprim hX3 hYXgl
        (Nm - a • (1 : Matrix (Fin n) (Fin n) K)) hZY hZ0 v
    have hZ : Nm - a • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      simpa only [Matrix.toLin'_apply, Matrix.zero_mulVec] using hZall v
    refine ⟨a, ?_⟩
    rw [sub_eq_zero] at hZ
    simpa only [hNm] using hZ
  have hAns : ¬ ∃ a : K, A = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rintro ⟨a, ha⟩
    apply hMns
    refine ⟨a, ?_⟩
    apply (LinearMap.toMatrix b b).injective
    rw [map_smul, LinearMap.toMatrix_one, ← hA, ha]
  have hA_quad : A * A = A.trace • A + A.trace ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) :=
    ggNSPosPF3C_mat2_quadratic hA3 hAns
  have hM_quad : M * M = A.trace • M + A.trace ^ 2 • (1 : V1 →ₗ[K] V1) := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_mul, map_add, map_smul, map_smul, LinearMap.toMatrix_one, ← hA]
    exact hA_quad
  set Z : Matrix (Fin n) (Fin n) K := Nm * Nm + A.trace • Nm + A.trace ^ 2 • 1 with hZdef
  have hZY : Z * Ym = Ym * Z := by
    rw [hZdef]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
    rw [show Nm * Nm * Ym = Ym * (Nm * Nm) from by
      rw [Matrix.mul_assoc, hNYm, ← Matrix.mul_assoc, hNYm, Matrix.mul_assoc], hNYm]
  have hZ0 : ∀ v ∈ V1, Z *ᵥ v = 0 := by
    intro v hv
    have hMM : ∀ w : V1, ((M * M) w : Fin n → K) = (Nm * Nm) *ᵥ (w : Fin n → K) := by
      intro w
      rw [Module.End.mul_apply, hM_apply, hM_apply, Matrix.mulVec_mulVec]
    have hquad : ∀ w : V1, ((M * M) w : Fin n → K) =
        A.trace • (Nm *ᵥ (w : Fin n → K)) + A.trace ^ 2 • (w : Fin n → K) := by
      intro w
      rw [hM_quad]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, hM_apply,
        Submodule.coe_add, Submodule.coe_smul]
    have hMMv : ((M * M) ⟨v, hv⟩ : Fin n → K) = (Nm * Nm) *ᵥ v := by
      simpa using hMM ⟨v, hv⟩
    have hquadv : ((M * M) ⟨v, hv⟩ : Fin n → K) =
        A.trace • (Nm *ᵥ v) + A.trace ^ 2 • v := by
      simpa using hquad ⟨v, hv⟩
    rw [hZdef]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [← hMMv, hquadv]
    have hkey : (A.trace • (Nm *ᵥ v) + A.trace ^ 2 • v) + A.trace • (Nm *ᵥ v) +
        A.trace ^ 2 • v = (A.trace • (Nm *ᵥ v) + A.trace ^ 2 • v) +
        (A.trace • (Nm *ᵥ v) + A.trace ^ 2 • v) := by abel
    rw [hkey, CharTwo.add_self_eq_zero]
  have hZall : ∀ v, Z *ᵥ v = 0 :=
    fun v => ggNSPosPF3C_mulVec_eq_zero_of_commute (p := 3) (by decide) hzprim hX3 hYXgl
      Z hZY hZ0 v
  have hZ : Z = 0 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simpa only [Matrix.toLin'_apply, Matrix.zero_mulVec] using hZall v
  have hfinal : Nm * Nm = A.trace • Nm + A.trace ^ 2 • (1 : Matrix (Fin n) (Fin n) K) := by
    have h1 : (Nm * Nm + A.trace • Nm) + A.trace ^ 2 • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [← hZdef]
      exact hZ
    have h2 : Nm * Nm + A.trace • Nm = A.trace ^ 2 • (1 : Matrix (Fin n) (Fin n) K) := by
      have hc := congrArg (fun X => X + A.trace ^ 2 • (1 : Matrix (Fin n) (Fin n) K)) h1
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at hc
      exact hc
    have h3 : Nm * Nm = A.trace • Nm + A.trace ^ 2 • (1 : Matrix (Fin n) (Fin n) K) := by
      have hc := congrArg (fun X => X + A.trace • Nm) h2
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at hc
      rw [add_comm] at hc
      exact hc
    exact h3
  have hτ : A.trace ≠ 0 := by
    intro hτ0
    have hNsq : Nm * Nm = 0 := by rw [hfinal, hτ0]; simp
    have hN3zero : Nm ^ 3 = 0 := by rw [pow_three, hNsq, Matrix.mul_zero]
    have h1 : (Nm ^ 3).det = 0 := by rw [hN3zero, Matrix.det_zero]
    have h2 : (Nm ^ 3).det ≠ 0 := by
      rw [Matrix.det_pow]
      exact pow_ne_zero 3 (by
        simpa only [hNm] using Matrix.GeneralLinearGroup.det_ne_zero N)
    exact h2 h1
  exact ⟨A.trace, hτ, by simpa only [hNm] using hfinal⟩

end CFSG.StandardType

end
