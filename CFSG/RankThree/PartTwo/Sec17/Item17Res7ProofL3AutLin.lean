module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Mat
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res7

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K]

@[expose] noncomputable def linearModelHom (q : ℕ) :
    SpecialLinearGroup (Fin 3) K →* projImage (slPi true 3 q K) :=
  (SpecialLinearGroup.toPGL : SpecialLinearGroup (Fin 3) K →* ProjGenLinGroup (Fin 3) K).codRestrict
    _ fun g => ⟨SpecialLinearGroup.toGL g, (mem_slPi_true q).mpr g.2, rfl⟩

theorem linearModelHom_surjective (q : ℕ) : Function.Surjective (linearModelHom (K := K) q) := by
  rintro ⟨_, A, hA, rfl⟩
  refine ⟨(⟨(A : Matrix (Fin 3) (Fin 3) K), (mem_slPi_true q).mp hA⟩ :
    SpecialLinearGroup (Fin 3) K), Subtype.ext ?_⟩
  change ProjGenLinGroup.mk (SpecialLinearGroup.toGL _) = ProjGenLinGroup.mk A
  congr 1
  exact Units.ext rfl

theorem ker_linearModelHom (q : ℕ) : (linearModelHom (K := K) q).ker = scalars 3 K := by
  ext g
  rw [MonoidHom.mem_ker, scalars_eq_center, ← SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

@[expose] noncomputable def linearModelEquiv (q : ℕ) :
    projectiveSL 3 K ≃* projImage (slPi true 3 q K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_linearModelHom q).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (linearModelHom_surjective q))

theorem coe_linearModelEquiv_proj (q : ℕ) (g : SpecialLinearGroup (Fin 3) K) :
    (linearModelEquiv q (proj 3 K g) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) :=
  rfl

theorem det_coe_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_diagTau, det_fin_three]
  simp
  linear_combination hτ

theorem det_coe_cycThree : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_cycThree, det_fin_three]
  simp

@[expose] def dSL {τ : K} (hτ : τ ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨(diagTau hτ : Matrix (Fin 3) (Fin 3) K), det_coe_diagTau hτ⟩

@[expose] def cSL : SpecialLinearGroup (Fin 3) K :=
  ⟨((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), det_coe_cycThree (K := K)⟩

theorem toGL_dSL {τ : K} (hτ : τ ^ 3 = 1) : SpecialLinearGroup.toGL (dSL hτ) = diagTau hτ :=
  Units.ext rfl

theorem toGL_cSL : SpecialLinearGroup.toGL (cSL : SpecialLinearGroup (Fin 3) K) = cycThree :=
  Units.ext rfl

theorem toGL_transpose_inv_dSL {τ : K} (hτ : τ ^ 3 = 1) :
    SpecialLinearGroup.toGL ((dSL hτ)⁻¹).transpose = (diagTau hτ)⁻¹ := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_transpose]
  have h : (((dSL hτ)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← SpecialLinearGroup.coe_GL_coe_matrix, map_inv, toGL_dSL]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toGL_transpose_inv_cSL :
    SpecialLinearGroup.toGL ((cSL : SpecialLinearGroup (Fin 3) K)⁻¹).transpose = cycThree := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_transpose]
  have h : (((cSL : SpecialLinearGroup (Fin 3) K)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (((cycThree : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
    rw [← SpecialLinearGroup.coe_GL_coe_matrix, map_inv, toGL_cSL]
  rw [h, coe_cycThree_inv, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_scalar_of_proj_eq {x y : SpecialLinearGroup (Fin 3) K}
    (h : proj 3 K x = proj 3 K y) :
    ∃ u : Kˣ, SpecialLinearGroup.toGL x = GeneralLinearGroup.scalar (Fin 3) u *
      SpecialLinearGroup.toGL y := by
  rw [proj_eq_proj_iff, scalars_eq_center, ← SpecialLinearGroup.toGL_mem_center_iff,
    GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  rw [map_mul, map_inv] at hu
  refine ⟨u⁻¹, ?_⟩
  have hy : SpecialLinearGroup.toGL y =
      SpecialLinearGroup.toGL x * GeneralLinearGroup.scalar (Fin 3) u := by
    rw [hu, mul_inv_cancel_left]
  rw [hy, map_inv, scalar_mul_comm, inv_mul_cancel_left]

theorem exists_scalar_of_conjAut_eq {A : GL (Fin 3) K} {g g' : SpecialLinearGroup (Fin 3) K}
    (h : conjAut 3 K A (proj 3 K g) = proj 3 K g') :
    ∃ u : Kˣ, A * SpecialLinearGroup.toGL g * A⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u * SpecialLinearGroup.toGL g' := by
  rw [conjAut_proj] at h
  obtain ⟨u, hu⟩ := exists_scalar_of_proj_eq h
  refine ⟨u, ?_⟩
  rw [← hu]
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation, Units.val_mul, Units.val_mul,
    SpecialLinearGroup.coe_GL_coe_matrix]

theorem ringEquiv_eq_one_of_card {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p)
    (σ : K ≃+* K) : σ = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (Fact.out : p.Prime).ne_zero)
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  set f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hbij : Function.Bijective f :=
    f.injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  have hσf : σ.toRingHom.comp f = f := RingHom.ext_zmod _ _
  refine RingEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := hbij.2 x
  exact DFunLike.congr_fun hσf y

variable [Finite K] {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ1 in
theorem autCent_projectiveSL {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p)
    (β : MulAut (projectiveSL 3 K)) (hd : β (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ))
    (hc : β (proj 3 K cSL) = proj 3 K cSL) :
    ∃ m j : ℕ, β = MulAut.conj (proj 3 K (dSL hτ) ^ m * proj 3 K cSL ^ j) := by
  obtain ⟨A, σ, ε, hε, hβ⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  rw [ringEquiv_eq_one_of_card hK σ, map_one, mul_one] at hβ
  interval_cases ε
  · rw [pow_zero, mul_one] at hβ
    obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq (hβ ▸ hd)
    obtain ⟨v, hv⟩ := exists_scalar_of_conjAut_eq (hβ ▸ hc)
    rw [toGL_dSL] at hu
    rw [toGL_cSL] at hv
    obtain ⟨s, m, j, hA⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
    refine ⟨m, j, ?_⟩
    rw [hβ, hA, map_mul, map_mul, conjAut_scalar, one_mul, map_pow, map_pow, ← toGL_dSL hτ,
      ← toGL_cSL, conjAut_toGL, conjAut_toGL, map_mul, map_pow, map_pow]
  · exfalso
    rw [pow_one] at hβ
    have hd' : conjAut 3 K A (proj 3 K ((dSL hτ)⁻¹).transpose) = proj 3 K (dSL hτ) := by
      rw [← dualAut_proj, ← MulAut.mul_apply, ← hβ, hd]
    have hc' : conjAut 3 K A (proj 3 K ((cSL : SpecialLinearGroup (Fin 3) K)⁻¹).transpose) =
        proj 3 K cSL := by
      rw [← dualAut_proj, ← MulAut.mul_apply, ← hβ, hc]
    obtain ⟨u, hu⟩ := exists_scalar_of_conjAut_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_conjAut_eq hc'
    rw [toGL_transpose_inv_dSL, toGL_dSL] at hu
    rw [toGL_transpose_inv_cSL, toGL_cSL] at hv
    exact false_of_conj_inv_hessian hτ hτ1 hu hv

end CFSG.RankThree.PartTwo.Sec17.Proof17Res7
