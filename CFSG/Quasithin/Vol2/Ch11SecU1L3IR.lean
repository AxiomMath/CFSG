module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module
open scoped MatrixGroups

theorem zmod_ringEquiv_subsingleton (p : ℕ) : Subsingleton (ZMod p ≃+* ZMod p) :=
  ⟨fun _ _ => RingEquiv.toRingHom_injective (RingHom.ext_zmod _ _)⟩

variable {K : Type} [Field K] [Finite K]

theorem conjAut_inner_of_pow_inner (A : GL (Fin 3) K) {k : ℕ} {g : projectiveSL 3 K}
    (h : LinearFlag.conjAut 3 K A ^ (2 ^ k) = MulAut.conj g) :
    ∃ g' : projectiveSL 3 K, LinearFlag.conjAut 3 K A = MulAut.conj g' := by
  obtain ⟨g₀, rfl⟩ := proj_surjective 3 K g
  rw [← map_pow, ← conjAut_toGL] at h
  have h1 : LinearFlag.conjAut 3 K (A ^ 2 ^ k * (Matrix.SpecialLinearGroup.toGL g₀)⁻¹) *
      LinearFlag.fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ 1 h1
  set d := Matrix.GeneralLinearGroup.det A with hd
  have hdc : d ^ 2 ^ k = c ^ 3 := by
    have h2 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [map_mul, map_inv, map_pow] at h2
    have hg : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g₀) = 1 :=
      Units.ext (by simp)
    rw [hg, inv_one, mul_one] at h2
    rw [← h2]
    apply Units.ext
    simp
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 2 ^ k + b * 3 = 1 := by
    have hcop : IsCoprime ((2 : ℤ) ^ k) 3 :=
      IsCoprime.pow_left (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
    obtain ⟨a, b, h⟩ := hcop
    exact ⟨a, b, h⟩
  have hm3 : (c ^ a * d ^ b) ^ 3 = d := by
    have h1 : d = d ^ (a * 2 ^ k + b * 3 : ℤ) := by rw [hab, zpow_one]
    have h2 : d ^ (a * 2 ^ k + b * 3 : ℤ) = (d ^ 2 ^ k) ^ a * (d ^ 3) ^ b := by
      rw [_root_.zpow_add, mul_comm a, mul_comm b, _root_.zpow_mul, _root_.zpow_mul]
      norm_cast
    rw [h2, hdc] at h1
    calc (c ^ a * d ^ b) ^ 3 = (c ^ 3) ^ a * (d ^ 3) ^ b := by
          rw [mul_pow, ← zpow_natCast (c ^ a), ← zpow_natCast (d ^ b), ← _root_.zpow_mul,
            ← _root_.zpow_mul, ← zpow_natCast c 3, ← zpow_natCast d 3, ← _root_.zpow_mul,
            ← _root_.zpow_mul, mul_comm a, mul_comm b]
      _ = d := h1.symm
  set m := c ^ a * d ^ b with hm
  set A' := Matrix.GeneralLinearGroup.scalar (Fin 3) m⁻¹ * A with hA'
  have hdetA' : ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det A' = 1 := by
      rw [hA', map_mul, ← hd]
      have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) m⁻¹) =
          m⁻¹ ^ 3 := Units.ext (by simp)
      rw [this, inv_pow, hm3, inv_mul_cancel]
    have := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  set S : SL(3, K) := ⟨_, hdetA'⟩ with hS
  refine ⟨proj 3 K S, ?_⟩
  have hAA' : A = Matrix.GeneralLinearGroup.scalar (Fin 3) m * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hgA' : Matrix.SpecialLinearGroup.toGL S = A' := Units.ext rfl
  rw [← conjAut_toGL, hgA', hAA', map_mul, conjAut_scalar, one_mul]

omit [Finite K] in
theorem mulVecLin_injective_of_GL (A : GL (Fin 3) K) :
    Function.Injective (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := by
  intro u v huv
  have h1 := congrArg (mulVecLin ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) huv
  simp only [mulVecLin_apply, mulVec_mulVec] at h1
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec] at h1

theorem inner_of_map_projStabilizer (p : ℕ) [Fact p.Prime] [CharP K p]
    [Subsingleton (K ≃+* K)] (α : MulAut (projectiveSL 3 K)) {k : ℕ} {g : projectiveSL 3 K}
    (hα : α ^ (2 ^ k) = MulAut.conj g) {W : Submodule K (Fin 3 → K)}
    (hW : finrank K W = 1 ∨ finrank K W = 2)
    (hP : (projStabilizer W).map (α : projectiveSL 3 K →* projectiveSL 3 K) =
      projStabilizer W) :
    ∃ g' : projectiveSL 3 K, α = MulAut.conj g' := by
  obtain ⟨A, σ, ε, hε, hαA⟩ := (automorphism_generation (n := 3) (K := K) le_rfl).2 α
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  interval_cases ε
  ·
    have hα0 : α = LinearFlag.conjAut 3 K A := by simpa using hαA
    rw [hα0] at hα ⊢
    exact conjAut_inner_of_pow_inner A hα
  ·
    exfalso
    have hα1 : α = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K := by simpa using hαA
    obtain ⟨-, -, -, -, -, -, hconj, -, hdual, -⟩ :=
      standard_automorphism_transport (n := 3) (K := K)
    have hmap : (projStabilizer W).map (α : projectiveSL 3 K →* projectiveSL 3 K) =
        projStabilizer ((dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) := by
      rw [hα1, ← hconj, ← hdual, Subgroup.map_map]
      rfl
    rw [hmap] at hP
    obtain ⟨-, hinj, -⟩ := maximal_parabolics (n := 3) (K := K) p (by norm_num)
    have hfr : finrank K ((dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) =
        3 - finrank K W := by
      rw [← (Submodule.equivMapOfInjective _ (mulVecLin_injective_of_GL A) (dotOrth W)).finrank_eq,
        finrank_dotOrth]
    have hW0 : ⊥ < W ∧ W < ⊤ := bot_lt_and_lt_top_of_finrank (by omega) (by omega)
    have hW1 : ⊥ < (dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) ∧
        (dotOrth W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) < ⊤ :=
      bot_lt_and_lt_top_of_finrank (by omega) (by omega)
    have heq := hinj hW1 hW0 hP
    rw [heq] at hfr
    omega

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
