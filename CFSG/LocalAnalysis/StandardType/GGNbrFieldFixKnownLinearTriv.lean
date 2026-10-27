module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearSub

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_one_of_fixes_subfield (hd : 3 ≤ d) (σ : K ≃+* K)
    {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    (h : ∀ g : LargeEvenSLGroup (Fin d) (fixF σ), φ (subfieldHom σ g) = subfieldHom σ g) :
    φ = 1 := by
  classical
  obtain ⟨A, -, hA⟩ := hφ
  have hscalarCenter : LargeEvenScalars (Fin d) K = Subgroup.center (GL (Fin d) K) :=
    largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm
  have hconj_mem : ∀ x : LargeEvenSLGroup (Fin d) K,
      A * (x : GL (Fin d) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin d) K := by
    intro x
    have hxdet : Matrix.GeneralLinearGroup.det (x : GL (Fin d) K) = 1 := by
      rw [← Units.val_eq_one, Matrix.GeneralLinearGroup.val_det_apply]
      exact TypeA.mem_largeEvenSLGroup_iff.mp x.2
    have hAdet : Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) = 1 := by
      rw [map_mul, map_mul, hxdet]
      simp
    refine TypeA.mem_largeEvenSLGroup_iff.mpr ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hAdet, Units.val_one]
  let f : GL (Fin d) (fixF σ) →* GL (Fin d) K := Matrix.GeneralLinearGroup.map (fixF σ).subtype
  let H1 : Subgroup (GL (Fin d) K) := (LargeEvenSLGroup (Fin d) (fixF σ)).map f
  have hH1 : ⁅H1, H1⁆ = H1 := by
    dsimp only [H1, f]
    rw [← Subgroup.map_commutator, commutator_slGroup (K := fixF σ) hd]
  have hcent : ∀ g ∈ H1, ⁅A, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    dsimp only [H1, f] at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    let xH : LargeEvenSLGroup (Fin d) K := subfieldInclusion σ ⟨x, hx⟩
    have hxH_eq : (xH : GL (Fin d) K) = f x := by
      simp only [xH, f, coe_subfieldInclusion]
    let xA : LargeEvenSLGroup (Fin d) K :=
      ⟨A * (xH : GL (Fin d) K) * A⁻¹, hconj_mem xH⟩
    have hfix : φ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) xH) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) xH := by
      simpa only [subfieldHom, MonoidHom.comp_apply, xH] using h ⟨x, hx⟩
    have hquot : LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) xA =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) xH :=
      (hA xH xA rfl).symm.trans hfix
    have hmemZ : xH⁻¹ * xA ∈
        (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K) :=
      QuotientGroup.eq.mp hquot.symm
    let z : GL (Fin d) K := ((xH⁻¹ * xA : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)
    have hzmem : z ∈ Subgroup.center (GL (Fin d) K) := by
      rw [← hscalarCenter]
      exact Subgroup.mem_subgroupOf.mp hmemZ
    have hz_eq : z = (xH : GL (Fin d) K)⁻¹ * (A * (xH : GL (Fin d) K) * A⁻¹) := rfl
    have hconj1 : (xH : GL (Fin d) K) * z * (xH : GL (Fin d) K)⁻¹ =
        ⁅A, (xH : GL (Fin d) K)⁆ := by
      rw [commutatorElement_def, hz_eq]
      group
    have hconj2 : (xH : GL (Fin d) K) * z * (xH : GL (Fin d) K)⁻¹ = z := by
      rw [Subgroup.mem_center_iff.mp hzmem (xH : GL (Fin d) K)]
      group
    have hfinal : ⁅A, f x⁆ = z := by
      rw [← hxH_eq]
      exact hconj1.symm.trans hconj2
    rw [hfinal]
    exact hzmem
  have hH1comm : ∀ g ∈ H1, Commute A g :=
    fun g hg => commute_of_commutator_mem_center hH1 hcent hg
  have helem_mem : ∀ (i j : Fin d) (hij : i ≠ j),
      ((elemSL K hij : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) ∈ H1 := by
    intro i j hij
    dsimp only [H1, f]
    rw [Subgroup.mem_map]
    exact ⟨((elemSL (fixF σ) hij : LargeEvenSLGroup (Fin d) (fixF σ)) : GL (Fin d) (fixF σ)),
      (elemSL (fixF σ) hij).2, map_elemSL (fixF σ) hij⟩
  have hAscalar : A ∈ LargeEvenScalars (Fin d) K :=
    mem_scalars_of_commute_elemSL A fun i j hij => hH1comm _ (helem_mem i j hij)
  have hAcenter : A ∈ Subgroup.center (GL (Fin d) K) := by
    rw [← hscalarCenter]
    exact hAscalar
  refine MulEquiv.ext fun y => ?_
  change φ y = y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change φ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y) =
    LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y
  let yA : LargeEvenSLGroup (Fin d) K :=
    ⟨A * (y : GL (Fin d) K) * A⁻¹, hconj_mem y⟩
  have h1 : φ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) yA := hA y yA rfl
  have hyA : yA = y := by
    apply Subtype.ext
    show A * (y : GL (Fin d) K) * A⁻¹ = (y : GL (Fin d) K)
    rw [← Subgroup.mem_center_iff.mp hAcenter (y : GL (Fin d) K)]
    group
  rw [h1, hyA]

end CFSG.StandardType.LinearFieldFix

end
