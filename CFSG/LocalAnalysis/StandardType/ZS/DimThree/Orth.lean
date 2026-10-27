module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthForm
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthRefl
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.ZS.DimThree

open Subgroup Matrix CFSG.RankThree.PartOne CFSG.RankThree.SubgroupLists
open CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma exists_root_of_sq_zo {Q : QuadraticForm (ZMod p) U} {t : U ≃ₗ[ZMod p] U}
    {u v : U} (htu : t u = -u) (h : ∃ s : ZMod p, Q v = s ^ 2 * Q u) :
    ∃ a : U, Q a = Q v ∧ t a = -a := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s • u, ?_, ?_⟩
  · rw [QuadraticMap.map_smul, smul_eq_mul, hs, pow_two]
  · rw [map_smul, htu, smul_neg]

private lemma exists_sq_mul_zo {x c : ZMod p} (hc : c ≠ 0) {s : ZMod p}
    (h : x * c = s * s) : ∃ s' : ZMod p, x = s' ^ 2 * c := by
  refine ⟨s * c⁻¹, ?_⟩
  refine mul_right_cancel₀ hc ?_
  have h1 : (s * c⁻¹) ^ 2 * c * c = s * s := by
    rw [pow_two]
    calc (s * c⁻¹) * (s * c⁻¹) * c * c = (s * s) * (c⁻¹ * c) * (c⁻¹ * c) := by ring
      _ = s * s := by rw [inv_mul_cancel₀ hc, mul_one, mul_one]
  rw [h, h1]

private lemma isSquare_mul_of_mul_not_isSquare_zo {F : Type*} [Field F] [Finite F]
    {x y c : F} (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0)
    (hxc : ¬ IsSquare (x * c)) (hyc : ¬ IsSquare (y * c)) : IsSquare (x * y) := by
  have h := CFSG.LocalAnalysis.ComponentInitial.isSquare_mul_of_not_isSquare
    (mul_ne_zero hx hc) (mul_ne_zero hy hc) hxc hyc
  have he : (x * c) * (y * c) = (x * y) * (c * c) := by ring
  rw [he] at h
  have hcc : IsSquare (c * c) := ⟨c, rfl⟩
  have h2 : IsSquare ((x * y) * (c * c) * (c * c)⁻¹) := h.mul hcc.inv
  rwa [mul_assoc, mul_inv_cancel₀ (mul_ne_zero hc hc), mul_one] at h2

private lemma le_isom_zo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A)
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ omegaGL M, g * x * g⁻¹ ∈ omegaGL M)
    (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype) :
    ∀ g ∈ A, IsIsom p (formOf e M) g := by
  have hle : A ≤ TauCeti.QuadraticMap.orthogonalGroup (formOf e M) := by
    rw [hR]
    refine (Subgroup.closure_le (TauCeti.QuadraticMap.orthogonalGroup (formOf e M))).mpr ?_
    rintro t ⟨htA, ht⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (isIsom_of_isRefl_of_normalizes hp e hMt hMd hirr ht
        (hn (autGL e t) (Subgroup.mem_map_of_mem (autGL e).toMonoidHom htA)))
  exact fun g hg => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hle hg)

private lemma commutator_mem_zo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hΩ : omegaGL M ≤ A.map (autGL e).toMonoidHom)
    {g t : U ≃ₗ[ZMod p] U} (hg : IsIsom p (formOf e M) g)
    (ht : IsIsom p (formOf e M) t) :
    t⁻¹ * g * t * g⁻¹ ∈ A := by
  have hti : IsIsom p (formOf e M) t⁻¹ :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (Subgroup.inv_mem _ (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ht))
  have hmem : autGL e (t⁻¹ * g * t * g⁻¹) ∈ omegaGL M := by
    have h := autGL_commutator_mem_omegaGL hp e hMt hMd (g := t⁻¹) (h := g) hti hg
    simpa using h
  have hG : autGL e (t⁻¹ * g * t * g⁻¹) ∈ A.map (autGL e).toMonoidHom := hΩ hmem
  have hpre := (Subgroup.mem_map_equiv (f := autGL e) (K := A)).mp hG
  simpa using hpre

private lemma conj_root_eq_zo (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g t r : U ≃ₗ[ZMod p] U} {u v : U}
    (hgI : IsIsom p Q g) (htR : IsRefl p t) (htI : IsIsom p Q t)
    (htu : t u = -u) (hgu : g u = v ∨ g u = -v) (hv : v ≠ 0)
    (hrR : IsRefl p r) (hrI : IsIsom p Q r) (hrv : r v = -v) :
    g * t * g⁻¹ = r := by
  have hinv : g⁻¹ = g.symm := rfl
  rw [hinv]
  have hSrefl : IsRefl p (g * t * g.symm) := by
    have h := htR.conj g
    rwa [hinv] at h
  have hSiso : IsIsom p Q (g * t * g.symm) := by
    intro w
    calc Q ((g * t * g.symm) w) = Q (g (t (g.symm w))) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = Q (t (g.symm w)) := hgI _
      _ = Q (g.symm w) := htI _
      _ = Q w := by
          have h := hgI (g.symm w)
          rw [LinearEquiv.apply_symm_apply] at h
          exact h.symm
  have hconj : (g * t * g.symm) (g u) = -(g u) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply, htu,
      map_neg]
  have hSv : (g * t * g.symm) v = -v := by
    rcases hgu with hgu | hgu
    · rwa [hgu] at hconj
    · rw [hgu, neg_neg] at hconj
      have h2 := congrArg (g * t * g.symm) hconj
      rw [← LinearEquiv.mul_apply, hSrefl.1] at h2
      simpa using h2.symm
  exact eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hSrefl hSiso hrR hrI hv hSv hrv

private lemma mem_of_root_eq_zo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    [Module.Finite (ZMod p) U]
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hΩ : omegaGL M ≤ A.map (autGL e).toMonoidHom)
    (hA : ∀ g ∈ A, IsIsom p (formOf e M) g)
    (hQ : (QuadraticMap.polarBilin (formOf e M)).Nondegenerate)
    {t r : U ≃ₗ[ZMod p] U} (htA : t ∈ A) (htR : IsRefl p t)
    {u v : U} (htu : t u = -u) (hu : (formOf e M) u ≠ 0)
    (hQv : (formOf e M) v = (formOf e M) u)
    (hrR : IsRefl p r) (hrI : IsIsom p (formOf e M) r) (hrv : r v = -v) : r ∈ A := by
  have hti : IsIsom p (formOf e M) t := hA t htA
  obtain ⟨g, hgI, hgu⟩ := exists_isIsom_apply_eq hp hu hQv.symm
  have hv : v ≠ 0 := by
    rintro rfl
    exact hu (by rw [← hQv]; exact QuadraticMap.map_zero _)
  have hEq := conj_root_eq_zo (Q := formOf e M) hp hQ hgI htR hti htu hgu hv hrR hrI hrv
  have hcomm := commutator_mem_zo hp e hMt hMd hΩ hgI hti
  have hmem : t * (t⁻¹ * g * t * g⁻¹) ∈ A := A.mul_mem htA hcomm
  have heq : t * (t⁻¹ * g * t * g⁻¹) = g * t * g⁻¹ := by group
  rw [heq, hEq] at hmem
  exact hmem

private lemma isOrthType_orth_zo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    [Module.Finite (ZMod p) U]
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hΩ : omegaGL M ≤ A.map (autGL e).toMonoidHom)
    (hA : ∀ g ∈ A, IsIsom p (formOf e M) g)
    (hQ : (QuadraticMap.polarBilin (formOf e M)).Nondegenerate)
    {t₀ : U ≃ₗ[ZMod p] U} (ht₀A : t₀ ∈ A) (ht₀R : IsRefl p t₀)
    {u₀ : U} (hu₀ : (formOf e M) u₀ ≠ 0) (hu₀r : t₀ u₀ = -u₀)
    {c : ZMod p} (hc : c = (formOf e M) u₀)
    {t₁ : U ≃ₗ[ZMod p] U} (ht₁A : t₁ ∈ A) (ht₁R : IsRefl p t₁)
    {u₁ : U} (hu₁ : (formOf e M) u₁ ≠ 0) (hu₁r : t₁ u₁ = -u₁)
    (hu₁ns : ¬ IsSquare ((formOf e M) u₁ * c)) : IsOrthType p A := by
  have hall : ∀ v : U, (formOf e M) v ≠ 0 → ∀ r : U ≃ₗ[ZMod p] U, IsRefl p r →
      IsIsom p (formOf e M) r → r v = -v → r ∈ A := by
    intro v hv r hrR hrI hrv
    by_cases hsq : IsSquare ((formOf e M) v * c)
    · obtain ⟨s, hs⟩ := hsq
      obtain ⟨s', hs'⟩ := exists_sq_mul_zo (by rw [hc]; exact hu₀) hs
      obtain ⟨a, hQa, hta⟩ := exists_root_of_sq_zo hu₀r ⟨s', by rw [hs', hc]⟩
      exact mem_of_root_eq_zo hp e hMt hMd hΩ hA hQ ht₀A ht₀R hta (by rw [hQa]; exact hv)
        hQa.symm hrR hrI hrv
    · have hsq1 : IsSquare ((formOf e M) v * (formOf e M) u₁) :=
        isSquare_mul_of_mul_not_isSquare_zo hv hu₁ (by rw [hc]; exact hu₀) hsq hu₁ns
      obtain ⟨s, hs⟩ := hsq1
      obtain ⟨s', hs'⟩ := exists_sq_mul_zo hu₁ hs
      obtain ⟨a, hQa, hta⟩ := exists_root_of_sq_zo hu₁r ⟨s', hs'⟩
      exact mem_of_root_eq_zo hp e hMt hMd hΩ hA hQ ht₁A ht₁R hta (by rw [hQa]; exact hv)
        hQa.symm hrR hrI hrv
  refine ⟨formOf e M, hQ, Or.inl fun g => ⟨fun hg => hA g hg, fun hg => ?_⟩⟩
  refine mem_of_isIsom_of_isRefl_mem hp hQ ?_ hg
  intro r hrR hrI
  obtain ⟨a, ha, hra⟩ := exists_root_of_isRefl_isIsom hp hQ hrR hrI
  exact hall a ha r hrR hrI hra

private lemma isOrthType_orthClass_zo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    [Module.Finite (ZMod p) U]
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A)
    (hΩ : omegaGL M ≤ A.map (autGL e).toMonoidHom)
    (hA : ∀ g ∈ A, IsIsom p (formOf e M) g)
    (hQ : (QuadraticMap.polarBilin (formOf e M)).Nondegenerate)
    {t₀ : U ≃ₗ[ZMod p] U} (ht₀A : t₀ ∈ A) (ht₀R : IsRefl p t₀)
    {u₀ : U} (hu₀ : (formOf e M) u₀ ≠ 0) (hu₀r : t₀ u₀ = -u₀)
    {c : ZMod p} (hc : c = (formOf e M) u₀)
    (hno : ∀ (t : U ≃ₗ[ZMod p] U), t ∈ A → IsRefl p t → ∀ a : U, (formOf e M) a ≠ 0 →
      t a = -a → IsSquare ((formOf e M) a * c)) : IsOrthType p A := by
  have hrefl : ∀ t : U ≃ₗ[ZMod p] U, t ∈ A → IsRefl p t →
      t ∈ ClassRefl p (formOf e M) c := by
    intro t htA htR
    refine ⟨htR, hA t htA, ?_⟩
    obtain ⟨a, ha, hta⟩ := exists_root_of_isRefl_isIsom hp hQ htR (hA t htA)
    obtain ⟨s, hs⟩ := hno t htA htR a ha hta
    obtain ⟨s', hs'⟩ := exists_sq_mul_zo (by rw [hc]; exact hu₀) hs
    have hs'0 : s' ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hs'
      exact ha hs'
    refine ⟨s'⁻¹ • a, ?_, ?_⟩
    · rw [QuadraticMap.map_smul, smul_eq_mul, hs']
      calc (s'⁻¹ * s'⁻¹) * (s' ^ 2 * c) = (s'⁻¹ * s') * (s'⁻¹ * s') * c := by ring
        _ = c := by rw [inv_mul_cancel₀ hs'0, one_mul, one_mul]
    · rw [map_smul, hta, smul_neg]
  have hmem : ClassRefl p (formOf e M) c ⊆ A := by
    rintro t ⟨htR, htI, a, ha, hta⟩
    refine mem_of_root_eq_zo hp e hMt hMd hΩ hA hQ ht₀A ht₀R hu₀r hu₀ ?_ htR htI hta
    rw [ha, hc]
  refine ⟨formOf e M, hQ, Or.inr ⟨c, by rw [hc]; exact hu₀, le_antisymm ?_ ?_⟩⟩
  · rw [hR]
    exact (Subgroup.closure_le (Subgroup.closure (ClassRefl p (formOf e M) c))).mpr
      fun t ht => Subgroup.subset_closure (hrefl t ht.1 ht.2)
  · exact (Subgroup.closure_le A).mpr hmem

private lemma isOrthType_core_zo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    [inst : Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    (hΩ : omegaGL M ≤ A.map (autGL e).toMonoidHom)
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ omegaGL M, g * x * g⁻¹ ∈ omegaGL M)
    (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype) : IsOrthType p A := by
  classical
  have hQ : (QuadraticMap.polarBilin (formOf e M)).Nondegenerate :=
    polarBilin_formOf_nondegenerate hp e hMt hMd
  have hA : ∀ g ∈ A, IsIsom p (formOf e M) g := le_isom_zo hp e hMt hMd hR hn hirr
  obtain ⟨tM, htM, htMr⟩ := exists_isRefl_mem hp e hR hI
  let t₀ : U ≃ₗ[ZMod p] U := (autGL e).symm tM
  have ht₀A : t₀ ∈ A := (Subgroup.mem_map_equiv (f := autGL e) (K := A)).mp htM
  have ht₀R : IsRefl p t₀ := (isRefl_iff_autGL hp e t₀).mpr (by simpa [t₀] using htMr)
  obtain ⟨u₀, hu₀, hu₀r⟩ := exists_root_of_isRefl_isIsom hp hQ ht₀R (hA t₀ ht₀A)
  by_cases hcase : ∃ t ∈ A, IsRefl p t ∧ ∃ a : U, (formOf e M) a ≠ 0 ∧ t a = -a ∧
      ¬ IsSquare ((formOf e M) a * (formOf e M) u₀)
  · obtain ⟨t₁, ht₁A, ht₁R, u₁, hu₁, hu₁r, hu₁ns⟩ := hcase
    exact isOrthType_orth_zo hp e hMt hMd hΩ hA hQ ht₀A ht₀R hu₀ hu₀r rfl ht₁A ht₁R hu₁ hu₁r hu₁ns
  · refine isOrthType_orthClass_zo hp e hMt hMd hR hΩ hA hQ ht₀A ht₀R hu₀ hu₀r rfl ?_
    intro t htA htR a ha hta
    by_contra h
    exact hcase ⟨t, htA, htR, a, ha, hta, h⟩

theorem isOrthType_of_omegaGL_le (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hMd : M.det ≠ 0)
    (hΩ : omegaGL M ≤ A.map (autGL e).toMonoidHom)
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ omegaGL M, g * x * g⁻¹ ∈ omegaGL M)
    (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype) : IsOrthType p A :=
  isOrthType_core_zo (inst := Module.Finite.equiv e.symm) hp e hR hI hMt hMd hΩ hn hirr

end CFSG.StandardType.ZS.DimThree
