module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

private lemma inv_mulVec_mulVec_D0 (a : GL ι K) (v : ι → K) :
    ((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ (((a : GL ι K) : Matrix ι ι K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

@[expose] def lineStab (Γ : Subgroup (GL ι K)) (w₀ : ι → K) : Subgroup ↥Γ where
  carrier := {γ | ∃ c : K, ((γ : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c • w₀}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨d * c, ?_⟩
    have hco : (((a * b : ↥Γ) : GL ι K) : Matrix ι ι K)
        = (((a : GL ι K) : Matrix ι ι K)) * (((b : GL ι K) : Matrix ι ι K)) := by
      rw [Subgroup.coe_mul, Units.val_mul]
    rw [hco, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul, hc, smul_smul]
  inv_mem' := by
    rintro a ⟨c, hc⟩
    by_cases hc0 : c = 0
    · refine ⟨0, ?_⟩
      have hw : w₀ = 0 := by
        rw [← inv_mulVec_mulVec_D0 (a : GL ι K) w₀, hc, hc0, zero_smul, Matrix.mulVec_zero]
      rw [hw, Matrix.mulVec_zero, zero_smul]
    · refine ⟨c⁻¹, ?_⟩
      have hv : c • ((((a⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ w₀) = w₀ := by
        rw [← Matrix.mulVec_smul, ← hc, Subgroup.coe_inv, inv_mulVec_mulVec_D0]
      conv_rhs => rw [← hv]
      rw [← mul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem mem_lineStab {Γ : Subgroup (GL ι K)} {w₀ : ι → K} {γ : ↥Γ} :
    γ ∈ lineStab Γ w₀ ↔ ∃ c : K, ((γ : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c • w₀ :=
  Iff.rfl

private lemma coe_inv_mul_self_D0 {Γ : Subgroup (GL ι K)} (x : ↥Γ) :
    (((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)
      * (((x : ↥Γ) : GL ι K) : Matrix ι ι K) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  rfl

private lemma coe_mul_inv_self_D0 {Γ : Subgroup (GL ι K)} (x : ↥Γ) :
    (((x : ↥Γ) : GL ι K) : Matrix ι ι K)
      * (((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  rfl

private lemma coe_inv_mul_mul_mul_D0 {Γ : Subgroup (GL ι K)} (x γ : ↥Γ) :
    (((x⁻¹ * γ * x : ↥Γ) : GL ι K) : Matrix ι ι K)
      = (((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) * (((γ : GL ι K) : Matrix ι ι K))
        * (((x : ↥Γ) : GL ι K) : Matrix ι ι K) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]

private lemma lineStab_mulVec_iff_D0 (Γ : Subgroup (GL ι K)) (x γ : ↥Γ) (w₀ : ι → K) :
    γ ∈ lineStab Γ (((x : GL ι K) : Matrix ι ι K) *ᵥ w₀) ↔
      x⁻¹ * γ * x ∈ lineStab Γ w₀ := by
  rw [mem_lineStab, mem_lineStab]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [coe_inv_mul_mul_mul_D0]
    calc (((((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) * (((γ : GL ι K) : Matrix ι ι K))
            * (((x : ↥Γ) : GL ι K) : Matrix ι ι K))) *ᵥ w₀
        = (((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)
            *ᵥ (((γ : GL ι K) : Matrix ι ι K)
              *ᵥ ((((x : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ w₀)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = (((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)
            *ᵥ (c • ((((x : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ w₀)) := by rw [hc]
      _ = c • ((((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)
            *ᵥ ((((x : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ w₀)) := by
          rw [Matrix.mulVec_smul]
      _ = c • (((((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)
            * (((x : ↥Γ) : GL ι K) : Matrix ι ι K)) *ᵥ w₀) := by
          rw [Matrix.mulVec_mulVec]
      _ = c • (1 *ᵥ w₀) := by rw [coe_inv_mul_self_D0]
      _ = c • w₀ := by rw [Matrix.one_mulVec]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h := congrArg (fun v => (((x : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v) hc
    rw [coe_inv_mul_mul_mul_D0, Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
    rw [show (((x : ↥Γ) : GL ι K) : Matrix ι ι K)
          * ((((x⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K)
            * (((γ : GL ι K) : Matrix ι ι K))
            * (((x : ↥Γ) : GL ι K) : Matrix ι ι K))
        = (((γ : GL ι K) : Matrix ι ι K))
          * (((x : ↥Γ) : GL ι K) : Matrix ι ι K) by
      rw [← mul_assoc, ← mul_assoc, coe_mul_inv_self_D0, one_mul]] at h
    rw [← Matrix.mulVec_mulVec] at h
    exact h

theorem lineStab_mulVec (Γ : Subgroup (GL ι K)) (x : ↥Γ) (w₀ : ι → K) :
    lineStab Γ (((x : GL ι K) : Matrix ι ι K) *ᵥ w₀) =
      (lineStab Γ w₀).map (MulAut.conj x).toMonoidHom := by
  ext γ
  rw [Subgroup.mem_map]
  constructor
  · intro hγ
    refine ⟨x⁻¹ * γ * x, (lineStab_mulVec_iff_D0 Γ x γ w₀).mp hγ, ?_⟩
    show MulAut.conj x (x⁻¹ * γ * x) = γ
    rw [MulAut.conj_apply]
    group
  · rintro ⟨δ, hδ, rfl⟩
    change MulAut.conj x δ ∈ lineStab Γ (((x : GL ι K) : Matrix ι ι K) *ᵥ w₀)
    refine (lineStab_mulVec_iff_D0 Γ x (MulAut.conj x δ) w₀).mpr ?_
    rwa [show x⁻¹ * MulAut.conj x δ * x = δ by rw [MulAut.conj_apply]; group]

@[expose] def pointStab {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) :
    Subgroup ↥H :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  MulAction.stabilizer ↥H ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
