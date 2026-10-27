module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.RankThree.PartOne.LIT.McMitchell
public import CFSG.RankThree.PartOne.N1322.CoreDefs
import CFSG.RankThree.PartOne.N1322.CaseBasic
public import CFSG.RankThree.PartOne.N1322.Mono
import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.StandardType.ZS.DimThree

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL autGL_mulVec)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem four_ne_zero_of_ne_two (hp : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [show (4 : ZMod p) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

private lemma sub_one_mulVecLin_autGL_zb {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] (e : V ≃ₗ[K] (Fin 3 → K)) (t : V ≃ₗ[K] V) :
    (((autGL e t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1).mulVecLin =
      (e : V →ₗ[K] (Fin 3 → K)) ∘ₗ ((t : V →ₗ[K] V) - LinearMap.id) ∘ₗ
        (e.symm : (Fin 3 → K) →ₗ[K] V) := by
  refine LinearMap.ext fun v => ?_
  simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, autGL_mulVec, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]
  simp

private lemma sub_one_rank_autGL_zb {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] (e : V ≃ₗ[K] (Fin 3 → K)) (t : V ≃ₗ[K] V) :
    (((autGL e t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1).rank =
      Module.finrank K (LinearMap.range ((t : V →ₗ[K] V) - LinearMap.id)) := by
  rw [show (((autGL e t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1).rank =
      Module.finrank K (LinearMap.range
        ((((autGL e t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1).mulVecLin)) from rfl]
  rw [sub_one_mulVecLin_autGL_zb, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

private lemma finrank_range_vecMulVec_zb {K : Type*} [Field K] {u v : Fin 3 → K}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    Module.finrank K (LinearMap.range (Matrix.vecMulVec u v).mulVecLin) = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  have hf : ((dotProductEquiv K (Fin 3)) v) ≠ 0 := by
    intro h0
    have h1 := dotProductEquiv_apply_apply K (Fin 3) v (Pi.single j 1)
    rw [h0] at h1
    simp only [LinearMap.zero_apply, dotProduct_single, mul_one] at h1
    exact hj h1.symm
  have hmv : (Matrix.vecMulVec u v).mulVecLin =
      ((dotProductEquiv K (Fin 3)) v).smulRight u := by
    refine LinearMap.ext fun w => ?_
    rw [Matrix.mulVecLin_apply, Matrix.vecMulVec_mulVec, LinearMap.smulRight_apply,
      dotProductEquiv_apply_apply]
    simp
  rw [hmv, LinearMap.range_smulRight_apply hf]
  exact finrank_span_singleton hu

theorem isRefl_iff_autGL (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (t : U ≃ₗ[ZMod p] U) : IsRefl p t ↔ N1322.IsRefl (autGL e t) := by
  have hrk := sub_one_rank_autGL_zb e t
  constructor
  · rintro ⟨h1, h2⟩
    exact N1322.isRefl_of_rank_one (by simpa using congrArg (autGL e) h1) (by rw [hrk]; exact h2)
  · intro h
    have hsq : autGL e t * autGL e t = 1 := N1322.IsRefl.sq h
    obtain ⟨r, φ, hr, hφ, hg⟩ := h
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have hφ0 : φ ≠ 0 := by
      intro h0
      have hφ' : (0 : ZMod p) = 2 := by simpa [h0] using hφ
      exact h2 hφ'.symm
    have hgm : ((autGL e t : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1 =
        Matrix.vecMulVec (-r) φ := by
      have h1 : (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) - Matrix.vecMulVec r φ - 1 =
          -Matrix.vecMulVec r φ := by abel
      rw [hg, h1]
      exact (Matrix.neg_vecMulVec r φ).symm
    refine ⟨?_, ?_⟩
    · exact (autGL e).injective (by simpa using hsq)
    · rw [← hrk, hgm]
      exact finrank_range_vecMulVec_zb (neg_ne_zero.mpr hr) hφ0

theorem det_autGL (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p)) (g : U ≃ₗ[ZMod p] U) :
    ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det =
      (LinearEquiv.det g : ZMod p) := by
  have h : LinearMap.toMatrix' ((e : U →ₗ[ZMod p] (Fin 3 → ZMod p)) ∘ₗ
      (g : U →ₗ[ZMod p] U) ∘ₗ (e.symm : (Fin 3 → ZMod p) →ₗ[ZMod p] U)) =
      ((autGL e g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    refine Matrix.mulVec_injective (funext fun v => ?_)
    rw [LinearMap.toMatrix'_mulVec]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact (autGL_mulVec e g v).symm
  rw [← h, LinearMap.det_toMatrix', LinearMap.det_conj, ← LinearEquiv.coe_det]

theorem map_autGL_eq_closure (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) :
    A.map (autGL e).toMonoidHom =
      Subgroup.closure {t | t ∈ A.map (autGL e).toMonoidHom ∧ N1322.IsRefl t} := by
  conv_lhs => rw [hR]
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ⟨htA, htrefl⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ htA, (isRefl_iff_autGL hp e t).mp htrefl⟩
  · rintro ⟨hx, hxrefl⟩
    obtain ⟨t, htA, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨t, ⟨htA, (isRefl_iff_autGL hp e t).mpr hxrefl⟩, rfl⟩

theorem isIrreducibleMatrixRep_map (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hI : AbsIrred p A) :
    IsIrreducibleMatrixRep (A.map (autGL e).toMonoidHom).subtype := by
  exact CFSG.RankThree.SubgroupLists.isIrreducibleOn_iff.mp
    (CFSG.RankThree.PartOne.LIT.isIrreducibleOn_map_autGL e hI.1)

theorem exists_isRefl_mem (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A) :
    ∃ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hempty : {t | t ∈ A ∧ IsRefl p t} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ht hrefl
    exact hcon (autGL e t) (Subgroup.mem_map_of_mem _ ht) ((isRefl_iff_autGL hp e t).mp hrefl)
  have hbot : A = ⊥ := by rw [hR, hempty, Subgroup.closure_empty]
  have hsingle : (Pi.single (0 : Fin 3) (1 : ZMod p) : Fin 3 → ZMod p) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp at h1
  have hvec : e.symm (Pi.single (0 : Fin 3) (1 : ZMod p)) ≠ 0 := by
    intro h
    rw [LinearEquiv.map_eq_zero_iff] at h
    exact hsingle h
  have hW : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) {e.symm (Pi.single (0 : Fin 3) (1 : ZMod p))}) = 1 :=
    finrank_span_singleton hvec
  have hinv : ∀ a ∈ A, ∀ w ∈ Submodule.span (ZMod p) {e.symm (Pi.single (0 : Fin 3) (1 : ZMod p))},
      a w ∈ Submodule.span (ZMod p) {e.symm (Pi.single (0 : Fin 3) (1 : ZMod p))} := by
    intro a ha w hw
    rw [hbot, Subgroup.mem_bot] at ha
    simpa [ha] using hw
  have hU : Module.finrank (ZMod p) U = 3 := by
    rw [LinearEquiv.finrank_eq e, Module.finrank_fin_fun]
  rcases hI.1 _ hinv with h | h
  · rw [h, finrank_bot] at hW
    omega
  · rw [h, finrank_top, hU] at hW
    omega

end CFSG.StandardType.ZS.DimThree
