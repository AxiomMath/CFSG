module

public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.OrthogonalInvolutions QuadraticMap Matrix

section Dickson

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem matrixLinearIso_apply (A : GL (Fin d) K) (v : Fin d → K) :
    matrixLinearIso A v = A.val *ᵥ v := rfl

theorem map_matrixDerived_linearIso :
    (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived Q := by
  rw [matrixDerived, Subgroup.map_commutator]
  have h : (matrixIsometries Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [matrixIsometries]
    exact Subgroup.map_comap_eq_self_of_surjective (matrixLinearIso (d := d) (K := K)).surjective _
  rw [h]

theorem map_mulVec_of_mem {γ : GL (Fin d) K} (hγ : γ ∈ matrixIsometries Q) (v : Fin d → K) :
    Q (γ.val *ᵥ v) = Q v := (mem_matrixIsometries_iff Q γ).1 hγ v

theorem polar_mulVec_of_mem {γ : GL (Fin d) K} (hγ : γ ∈ matrixIsometries Q)
    (u v : Fin d → K) : polar Q (γ.val *ᵥ u) (γ.val *ᵥ v) = polar Q u v := by
  simp only [polar, ← Matrix.mulVec_add, map_mulVec_of_mem hγ]

section DicksonKernel

variable [Finite K] [CharP K 2]

theorem mem_matrixDerived_iff (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (B : GL (Fin d) K) :
    B ∈ matrixDerived Q ↔ matrixLinearIso B ∈ omegaGroup Q hnd := by
  have hEq : CFSG.RankThree.Classical2.orthDerived Q = omegaGroup Q hnd :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hnd hT)
  rw [← hEq, ← map_matrixDerived_linearIso]
  exact (Subgroup.mem_map_iff_mem (matrixLinearIso (d := d) (K := K)).injective).symm

theorem mem_matrixDerived_iff_even (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {B : GL (Fin d) K} (hB : B ∈ matrixIsometries Q) :
    B ∈ matrixDerived Q ↔ Even (Module.finrank K (commSpace (matrixLinearIso B))) := by
  rw [mem_matrixDerived_iff hnd hT, mem_omegaGroup]
  exact ⟨fun h => h.2, fun h => ⟨hB, h⟩⟩

end DicksonKernel

end Dickson

section Reflection

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

variable (Q) in
@[expose] noncomputable def reflMat (w : Fin d → K) (hw : Q w ≠ 0) : GL (Fin d) K :=
  letI : Invertible (Q w) := invertibleOfNonzero hw
  matrixLinearIso.symm (TauCeti.QuadraticMap.reflection Q w)

theorem reflMat_mulVec (w : Fin d → K) (hw : Q w ≠ 0) (x : Fin d → K) :
    (reflMat Q w hw).val *ᵥ x = x - (polar Q w x / Q w) • w := by
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  have h : matrixLinearIso (reflMat Q w hw) x = TauCeti.QuadraticMap.reflection Q w x := by
    rw [reflMat, MulEquiv.apply_symm_apply]
  rw [← matrixLinearIso_apply, h, TauCeti.QuadraticMap.reflection_apply_eq_sub_div]

theorem matrixLinearIso_reflMat (w : Fin d → K) (hw : Q w ≠ 0) :
    matrixLinearIso (reflMat Q w hw) =
      let _ : Invertible (Q w) := invertibleOfNonzero hw
      TauCeti.QuadraticMap.reflection Q w := by
  rw [reflMat, MulEquiv.apply_symm_apply]

theorem reflMat_mem_isometries (w : Fin d → K) (hw : Q w ≠ 0) :
    reflMat Q w hw ∈ matrixIsometries Q := by
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  change matrixLinearIso (reflMat Q w hw) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  rw [matrixLinearIso_reflMat]
  exact TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q w

theorem reflMat_mul_self (w : Fin d → K) (hw : Q w ≠ 0) :
    reflMat Q w hw * reflMat Q w hw = 1 := by
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  apply matrixLinearIso.injective
  rw [map_mul, matrixLinearIso_reflMat, TauCeti.QuadraticMap.reflection_mul_self, map_one]

theorem reflMat_congr {u w : Fin d → K} (h : u = w) (hu : Q u ≠ 0) (hw : Q w ≠ 0) :
    reflMat Q u hu = reflMat Q w hw := by
  subst h
  rfl

theorem finrank_commSpace_reflMat (hnd : Q.polarBilin.Nondegenerate) (w : Fin d → K)
    (hw : Q w ≠ 0) : Module.finrank K (commSpace (matrixLinearIso (reflMat Q w hw))) = 1 := by
  let _ : Invertible (Q w) := invertibleOfNonzero hw
  rw [matrixLinearIso_reflMat]
  exact finrank_commSpace_reflection hnd w

theorem conj_reflMat {γ : GL (Fin d) K} (hγ : γ ∈ matrixIsometries Q) (w : Fin d → K)
    (hw : Q w ≠ 0) (hw' : Q (γ.val *ᵥ w) ≠ 0) :
    γ * reflMat Q w hw * γ⁻¹ = reflMat Q (γ.val *ᵥ w) hw' := by
  apply matrixLinearIso.injective
  refine LinearEquiv.ext fun x => ?_
  have hinv : γ.val *ᵥ (γ⁻¹).val *ᵥ x = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, matrixLinearIso_apply,
    matrixLinearIso_apply, matrixLinearIso_apply, reflMat_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, hinv]
  change x - (polar Q w ((γ⁻¹).val *ᵥ x) / Q w) • (γ.val *ᵥ w) =
    (reflMat Q (γ.val *ᵥ w) hw').val *ᵥ x
  rw [reflMat_mulVec, map_mulVec_of_mem hγ]
  congr 3
  have := polar_mulVec_of_mem hγ w ((γ⁻¹).val *ᵥ x)
  rw [hinv] at this
  exact this.symm

section ReflectionDickson

variable [Finite K] [CharP K 2]

theorem reflMat_not_mem_derived (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (w : Fin d → K) (hw : Q w ≠ 0) : reflMat Q w hw ∉ matrixDerived Q := by
  rw [mem_matrixDerived_iff_even hnd hT (reflMat_mem_isometries w hw),
    finrank_commSpace_reflMat hnd w hw]
  decide

theorem mul_reflMat_mem_iff (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {B : GL (Fin d) K} (hB : B ∈ matrixIsometries Q) (w : Fin d → K) (hw : Q w ≠ 0) :
    B * reflMat Q w hw ∈ matrixDerived Q ↔ B ∉ matrixDerived Q := by
  have hr := reflMat_mem_isometries w hw
  rw [mem_matrixDerived_iff_even hnd hT (mul_mem hB hr), mem_matrixDerived_iff_even hnd hT hB,
    ← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even]
  have hmul := natCast_finrank_commSpace_mul hnd (g := matrixLinearIso B)
    (h := matrixLinearIso (reflMat Q w hw)) hB hr
  rw [← map_mul] at hmul
  rw [hmul, finrank_commSpace_reflMat hnd w hw, Nat.cast_one]
  generalize ((Module.finrank K (commSpace (matrixLinearIso B)) : ℕ) : ZMod 2) = x
  revert x
  decide

theorem mem_or_mul_reflMat_mem (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {B : GL (Fin d) K} (hB : B ∈ matrixIsometries Q) (w : Fin d → K) (hw : Q w ≠ 0) :
    B ∈ matrixDerived Q ∨ B * reflMat Q w hw ∈ matrixDerived Q := by
  by_cases h : B ∈ matrixDerived Q
  · exact Or.inl h
  · exact Or.inr ((mul_reflMat_mem_iff hnd hT hB w hw).2 h)

theorem mul_self_mem_matrixDerived (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {B : GL (Fin d) K} (hB : B ∈ matrixIsometries Q) : B * B ∈ matrixDerived Q := by
  rw [mem_matrixDerived_iff_even hnd hT (mul_mem hB hB), ← ZMod.natCast_eq_zero_iff_even]
  have hmul := natCast_finrank_commSpace_mul hnd (g := matrixLinearIso B)
    (h := matrixLinearIso B) hB hB
  rw [← map_mul] at hmul
  rw [hmul]
  exact CharTwo.add_self_eq_zero _

theorem reflMat_mul_reflMat_mem (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (w w' : Fin d → K) (hw : Q w ≠ 0) (hw' : Q w' ≠ 0) :
    reflMat Q w' hw' * reflMat Q w hw ∈ matrixDerived Q :=
  (mul_reflMat_mem_iff hnd hT (reflMat_mem_isometries w' hw') w hw).2
    (reflMat_not_mem_derived hnd hT w' hw')

end ReflectionDickson

section Norm1

variable [CharP K 2]

theorem reflMat_mulVec_one (w : Fin d → K) (hw : Q w = 1) (hw0 : Q w ≠ 0) (x : Fin d → K) :
    (reflMat Q w hw0).val *ᵥ x = x + polar Q w x • w := by
  rw [reflMat_mulVec, hw, div_one, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem eq_of_reflMat_eq (hnd : Q.polarBilin.Nondegenerate) {u w : Fin d → K}
    (hu : Q u = 1) (hw : Q w = 1) (hu0 : Q u ≠ 0) (hw0 : Q w ≠ 0)
    (h : reflMat Q u hu0 = reflMat Q w hw0) : u = w := by
  have hu' : u ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hu
    exact zero_ne_one hu
  obtain ⟨x, hx⟩ : ∃ x, polar Q u x ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hu' (hnd.1 u fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hall y
  have h1 : polar Q u x • u = polar Q w x • w := by
    have := congrArg (fun A : GL (Fin d) K => A.val *ᵥ x) h
    simp only [reflMat_mulVec_one u hu hu0, reflMat_mulVec_one w hw hw0] at this
    exact add_left_cancel this
  have h2 : u = (polar Q w x / polar Q u x) • w := by
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hx, one_smul]
  have h3 : (polar Q w x / polar Q u x) * (polar Q w x / polar Q u x) = 1 := by
    have := congrArg Q h2
    rw [QuadraticMap.map_smul, hu, hw, smul_eq_mul, mul_one] at this
    exact this.symm
  have h4 : polar Q w x / polar Q u x = 1 := by
    have h2c : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (polar Q w x / polar Q u x - 1) ^ 2 = 0 := by
      linear_combination h3 + (1 - polar Q w x / polar Q u x) * h2c
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  rw [h4, one_smul] at h2
  exact h2

theorem comm_reflMat_iff (hnd : Q.polarBilin.Nondegenerate) {γ : GL (Fin d) K}
    (hγ : γ ∈ matrixIsometries Q) {w : Fin d → K} (hw : Q w = 1) (hw0 : Q w ≠ 0) :
    γ * reflMat Q w hw0 = reflMat Q w hw0 * γ ↔ γ.val *ᵥ w = w := by
  have hγw : Q (γ.val *ᵥ w) = 1 := by rw [map_mulVec_of_mem hγ, hw]
  have hγw0 : Q (γ.val *ᵥ w) ≠ 0 := by rw [hγw]; exact one_ne_zero
  have hconj := conj_reflMat hγ w hw0 hγw0
  constructor
  · intro hc
    have : γ * reflMat Q w hw0 * γ⁻¹ = reflMat Q w hw0 := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [this] at hconj
    exact (eq_of_reflMat_eq hnd hγw hw hγw0 hw0 hconj.symm)
  · intro hfix
    have h1 : γ * reflMat Q w hw0 * γ⁻¹ = reflMat Q w hw0 := by
      rw [hconj]
      exact reflMat_congr hfix hγw0 hw0
    calc γ * reflMat Q w hw0 = γ * reflMat Q w hw0 * γ⁻¹ * γ := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = reflMat Q w hw0 * γ := by rw [h1]

end Norm1

end Reflection

end CFSG.RankThree.PartOne.AUTSL
