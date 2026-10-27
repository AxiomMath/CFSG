module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_conj_of_commute (hd : 3 ≤ d) {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f)
    {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    (hc : φ * f = f * φ) :
    ∃ B : GL (Fin d) (fixF σ), ∀ g g' : LargeEvenSLGroup (Fin d) (fixF σ),
      (g' : GL (Fin d) (fixF σ)) = B * g * B⁻¹ → φ (subfieldHom σ g) = subfieldHom σ g' := by
  obtain ⟨A, -, hA⟩ := hφ
  have hmem : ∀ x : LargeEvenSLGroup (Fin d) K,
      A * (x : GL (Fin d) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin d) K := by
    intro x
    rw [TypeA.mem_largeEvenSLGroup_iff]
    have hx : Matrix.GeneralLinearGroup.det (x : GL (Fin d) K) = 1 := by
      apply Units.ext
      rw [Units.val_one]
      exact TypeA.mem_largeEvenSLGroup_iff.mp x.2
    have hdet : Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hx]
      group
    change ((Matrix.GeneralLinearGroup.det (A * (x : GL (Fin d) K) * A⁻¹) : Kˣ) : K) = 1
    rw [hdet]
    exact Units.val_one
  let conjA : LargeEvenSLGroup (Fin d) K → LargeEvenSLGroup (Fin d) K :=
    fun x => ⟨A * (x : GL (Fin d) K) * A⁻¹, hmem x⟩
  have conjA_val : ∀ x : LargeEvenSLGroup (Fin d) K,
      ((conjA x : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) =
        A * (x : GL (Fin d) K) * A⁻¹ := fun _ => rfl
  let ρ : MulAut (LargeEvenSLGroup (Fin d) K) :=
    matAct (LargeEvenSLGroup (Fin d) K) (slMapStable d K) σ
  have hc_apply : ∀ x : LargeEvenSLGroup (Fin d) K,
      φ (f ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) x)) =
        f (φ ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) x)) := by
    intro x
    have h := congrArg (fun ψ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) =>
      ψ ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) x)) hc
    simpa only [MulAut.mul_apply] using h
  set S : GL (Fin d) K := Matrix.GeneralLinearGroup.map σ.toRingHom A with hSdef
  set T : GL (Fin d) K := A⁻¹ * S with hTdef
  have hcenter_x : ∀ x : LargeEvenSLGroup (Fin d) K,
      ⁅((ρ x : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)⁻¹, T⁆ ∈
        Subgroup.center (GL (Fin d) K) := by
    intro x
    have hstep : (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (conjA (ρ x)) =
        (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (ρ (conjA x)) := by
      calc (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (conjA (ρ x))
          = φ ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (ρ x)) :=
            (hA (ρ x) (conjA (ρ x)) rfl).symm
        _ = φ (f ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) x)) :=
              congrArg φ (hf x).symm
        _ = f (φ ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) x)) := hc_apply x
        _ = f ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (conjA x)) := by
              rw [hA x (conjA x) rfl]
        _ = (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (ρ (conjA x)) := hf (conjA x)
    have hZ := QuotientGroup.eq.mp hstep
    have hZgl : ((conjA (ρ x) : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)⁻¹ *
        ((ρ (conjA x) : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) ∈
        LargeEvenScalars (Fin d) K := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (Subgroup.mem_subgroupOf.mp hZ)
    have h2 : ((ρ (conjA x) : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) =
        S * ((ρ x : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) * S⁻¹ := by
      rw [matAct_coe (LargeEvenSLGroup (Fin d) K) (slMapStable d K) σ (conjA x),
        conjA_val x, Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv,
        matAct_coe (LargeEvenSLGroup (Fin d) K) (slMapStable d K) σ x, hSdef]
    rw [conjA_val, h2] at hZgl
    have hEk : A * ⁅((ρ x : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)⁻¹, T⁆ *
        A⁻¹ ∈ LargeEvenScalars (Fin d) K := by
      convert hZgl using 1
      rw [hTdef, commutatorElement_def]
      group
    have hcenter : A * ⁅((ρ x : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)⁻¹, T⁆ *
        A⁻¹ ∈ Subgroup.center (GL (Fin d) K) := by
      simpa only [largeEvenScalars_def, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        using hEk
    have hconj := Subgroup.Normal.conj_mem'
      (inferInstance : (Subgroup.center (GL (Fin d) K)).Normal)
      (A * ⁅((ρ x : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K)⁻¹, T⁆ * A⁻¹) hcenter A
    convert hconj using 1
    group
  have hcomm : ∀ g ∈ LargeEvenSLGroup (Fin d) K,
      ⁅T, g⁆ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g hg
    have h1 : ⁅g, T⁆ ∈ Subgroup.center (GL (Fin d) K) := by
      let y : LargeEvenSLGroup (Fin d) K :=
        ⟨g⁻¹, (LargeEvenSLGroup (Fin d) K).inv_mem hg⟩
      have h := hcenter_x (ρ.symm y)
      rw [ρ.apply_symm_apply] at h
      dsimp only [y] at h
      simpa using h
    rw [← commutatorElement_inv g T]
    exact (Subgroup.center (GL (Fin d) K)).inv_mem h1
  have hT : T ∈ LargeEvenScalars (Fin d) K :=
    mem_scalars_of_commute_elemSL T (fun i j hij =>
      commute_of_commutator_mem_center (commutator_slGroup hd) hcomm (elemSL K hij).2)
  rw [largeEvenScalars_def] at hT
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hT
  have hS : Matrix.GeneralLinearGroup.map σ.toRingHom A =
      A * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    rw [hc, hTdef, hSdef]
    group
  have hmat : ((Matrix.GeneralLinearGroup.map σ.toRingHom A : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (c : K) • (A : Matrix (Fin d) (Fin d) K) := by
    rw [hS, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨μ, B, hdesc⟩ := exists_descend_of_map_eq_smul σ A c hmat
  refine ⟨B, fun g g' hgg' => ?_⟩
  have hBmap : Matrix.GeneralLinearGroup.map (fixF σ).subtype B =
      Matrix.GeneralLinearGroup.scalar (Fin d) μ * A := by
    apply Units.ext
    rw [hdesc, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hmap : Matrix.GeneralLinearGroup.map (fixF σ).subtype g' =
      A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹ := by
    have h1 : Matrix.GeneralLinearGroup.map (fixF σ).subtype g' =
        Matrix.GeneralLinearGroup.map (fixF σ).subtype B *
          Matrix.GeneralLinearGroup.map (fixF σ).subtype g *
          (Matrix.GeneralLinearGroup.map (fixF σ).subtype B)⁻¹ := by
      conv_lhs => rw [hgg']
      rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv]
    rw [h1, hBmap]
    calc (Matrix.GeneralLinearGroup.scalar (Fin d) μ * A) *
            Matrix.GeneralLinearGroup.map (fixF σ).subtype g *
            (Matrix.GeneralLinearGroup.scalar (Fin d) μ * A)⁻¹
        = Matrix.GeneralLinearGroup.scalar (Fin d) μ *
            (A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin d) μ)⁻¹ := by
          rw [mul_inv_rev]
          group
      _ = (A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹) *
            Matrix.GeneralLinearGroup.scalar (Fin d) μ *
            (Matrix.GeneralLinearGroup.scalar (Fin d) μ)⁻¹ := by
          rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = A * Matrix.GeneralLinearGroup.map (fixF σ).subtype g * A⁻¹ := by group
  have hx' : (subfieldInclusion σ g' : LargeEvenSLGroup (Fin d) K) =
      conjA (subfieldInclusion σ g) := by
    apply Subtype.ext
    rw [coe_subfieldInclusion, conjA_val, coe_subfieldInclusion]
    exact hmap
  have hφx : φ ((LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))
        (subfieldInclusion σ g)) =
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (subfieldInclusion σ g') :=
    hA (subfieldInclusion σ g) (subfieldInclusion σ g') (by
      change ((subfieldInclusion σ g' : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) =
        A * ((subfieldInclusion σ g : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) * A⁻¹
      rw [hx', conjA_val])
  simpa only [subfieldHom, MonoidHom.comp_apply] using hφx

end CFSG.StandardType.LinearFieldFix

end
