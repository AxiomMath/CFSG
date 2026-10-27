module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutGens
import CFSG.LocalAnalysis.StandardType.GGQ2SignedPermMem

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.StandardType CFSG.StandardType.SpJoin Matrix Multiplicative
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
  {t : ℕ} {ε : Fin 2}

private theorem planeMat_sub (M M' : Fin t → Matrix (Fin 2) (Fin 2) K) :
    WitSpNs.planeMat M - WitSpNs.planeMat M' = WitSpNs.planeMat (M - M') := by
  calc WitSpNs.planeMat M - WitSpNs.planeMat M'
      = WitSpNs.planeMat M + (-1 : K) • WitSpNs.planeMat M' := by
        rw [sub_eq_add_neg, neg_one_smul]
    _ = WitSpNs.planeMat M + WitSpNs.planeMat ((-1 : K) • M') := by
        rw [SpBlocks.planeMat_smul]
        rfl
    _ = WitSpNs.planeMat (M + (-1 : K) • M') := by
        rw [SpBlocks.planeMat_add]
    _ = WitSpNs.planeMat (M - M') := by
        congr 1
        ext j
        simp [Matrix.sub_apply, sub_eq_add_neg]

theorem linTorusAutSubsetSignedPerm_holds : LinTorusAutSubsetSignedPerm := by
  intro K _ _ _ ζ t ε hK hζ X φ hφ
  obtain ⟨y, -, hy⟩ := hφ
  classical
  set Y : Matrix (LinIdx t ε) (LinIdx t ε) K :=
    ((y : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) with hY
  let M : PlaneRaw.V t → Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K :=
    fun u => WitSpNs.planeMat (fun j => ((ζ (Multiplicative.ofAdd (u j)) :
      SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
  have htau : ∀ u, ((tau ζ t ε u : GL (LinIdx t ε) K) :
      Matrix (LinIdx t ε) (LinIdx t ε) K) = Matrix.fromBlocks (M u) 0 0 1 :=
    fun u => coe_tau_eq_fromBlocks_planeMat (K := K) ζ t ε u
  obtain ⟨A, B, C, D, hYblocks⟩ : ∃ A B C D, Y = Matrix.fromBlocks A B C D :=
    ⟨Y.toBlocks₁₁, Y.toBlocks₁₂, Y.toBlocks₂₁, Y.toBlocks₂₂,
      (Matrix.fromBlocks_toBlocks Y).symm⟩
  have hblocks : ∀ u : PlaneRaw.V t,
      A * M u = M (φ u) * A ∧ B = M (φ u) * B ∧ C * M u = C := by
    intro u
    have h1 : y * tau ζ t ε u = tau ζ t ε (φ u) * y := by
      rw [← hy u]
      group
    have h2 := congrArg (fun z : GL (LinIdx t ε) K =>
      (z : Matrix (LinIdx t ε) (LinIdx t ε) K)) h1
    simp only [Units.val_mul] at h2
    rw [← hY, hYblocks, htau u, htau (φ u), Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply] at h2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul] at h2
    exact ⟨(Matrix.fromBlocks_inj.mp h2).1, (Matrix.fromBlocks_inj.mp h2).2.1,
      (Matrix.fromBlocks_inj.mp h2).2.2.1⟩
  let T : SpecialLinearGroup (Fin 2) K := ζ (Multiplicative.ofAdd (1 : ZMod 3))
  have hTne : T ≠ 1 := by
    intro h
    have h1 : ζ (Multiplicative.ofAdd (1 : ZMod 3)) = ζ 1 := by
      dsimp only [T] at h
      rw [h, map_one]
    exact one_ne_zero (ofAdd_eq_one.mp (hζ h1))
  have hTpow : T ^ 3 = 1 := by
    dsimp only [T]
    have h : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by
      rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
    rw [← map_pow, h, map_one]
  have htrace : ((T : Matrix (Fin 2) (Fin 2) K)).trace ≠ 0 :=
    trace_ne_zero_of_pow_eq_one hTne (by decide : Odd 3) hTpow
  have hdet : ((T : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 := by
    rw [TorC.det_sub_one_eq_trace]
    exact htrace
  let E : Matrix (Fin 2) (Fin 2) K := (T : Matrix (Fin 2) (Fin 2) K) - 1
  let Eunit : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero E hdet
  have hEunit : (Eunit : Matrix (Fin 2) (Fin 2) K) = E :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero E hdet
  have hQ : WitSpNs.planeMat (fun _ : Fin t => (T : Matrix (Fin 2) (Fin 2) K)) - 1 =
      WitSpNs.planeMat (fun _ : Fin t => E) := by
    rw [show (1 : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) =
        WitSpNs.planeMat (fun _ : Fin t => (1 : Matrix (Fin 2) (Fin 2) K)) from
      WitSpNs.planeMat_one.symm]
    rw [planeMat_sub]
    rfl
  let Q : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K := WitSpNs.planeMat (fun _ : Fin t => E)
  have hQleft : Q * WitSpNs.planeMat (fun _ : Fin t =>
      ((Eunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    dsimp only [Q]
    rw [WitSpNs.planeMat_mul]
    simp [← hEunit, WitSpNs.planeMat_one]
  have hQright : WitSpNs.planeMat (fun _ : Fin t =>
      ((Eunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * Q = 1 := by
    dsimp only [Q]
    rw [WitSpNs.planeMat_mul]
    simp [← hEunit, WitSpNs.planeMat_one]
  let Qunit : (Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)ˣ :=
    ⟨Q, WitSpNs.planeMat (fun _ : Fin t =>
      ((Eunit⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)), hQleft, hQright⟩
  have hCzero : C = 0 := by
    have h := (hblocks (fun _ : Fin t => (1 : ZMod 3))).2.2
    have hMT : M (fun _ : Fin t => (1 : ZMod 3)) =
        WitSpNs.planeMat (fun _ : Fin t => (T : Matrix (Fin 2) (Fin 2) K)) := rfl
    rw [hMT] at h
    have h0 : C * Q = 0 := by
      dsimp only [Q]
      rw [← hQ, Matrix.mul_sub, Matrix.mul_one, h, sub_self]
    calc C = C * (1 : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) := by simp
      _ = C * ((Qunit : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
            ((Qunit⁻¹ : (Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)ˣ) :
              Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)) := by
          rw [Units.mul_inv]
      _ = (C * Q) * ((Qunit⁻¹ : (Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)ˣ) :
            Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) := by
          rw [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.zero_mul]
  have hBzero : B = 0 := by
    have h := (hblocks (φ.symm (fun _ : Fin t => (1 : ZMod 3)))).2.1
    have hφ : φ (φ.symm (fun _ : Fin t => (1 : ZMod 3))) = fun _ : Fin t => (1 : ZMod 3) :=
      LinearEquiv.apply_symm_apply φ _
    have hMT : M (fun _ : Fin t => (1 : ZMod 3)) =
        WitSpNs.planeMat (fun _ : Fin t => (T : Matrix (Fin 2) (Fin 2) K)) := rfl
    rw [hφ, hMT] at h
    have h0 : Q * B = 0 := by
      dsimp only [Q]
      rw [← hQ, Matrix.sub_mul, Matrix.one_mul, h.symm, sub_self]
    calc B = (1 : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) * B := by simp
      _ = (((Qunit⁻¹ : (Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)ˣ) :
              Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
            (Qunit : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)) * B := by
          rw [Units.inv_mul]
      _ = ((Qunit⁻¹ : (Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)ˣ) :
            Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) * (Q * B) := by
          rw [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  have hYunit : IsUnit Y := ⟨y, hY.symm⟩
  have hYdet : Y.det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det Y).mp hYunit)
  have hdetA : A.det ≠ 0 := by
    intro h0
    apply hYdet
    rw [hYblocks, hBzero, hCzero, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]
  let Aunit : GL (Fin t ⊕ Fin t) K := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA
  have hAval : (Aunit : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hdetA
  have hAeq : ∀ u : PlaneRaw.V t,
      Aunit * (spPlaneTorus t ζ (fun i => Multiplicative.ofAdd (u i)) :
        GL (Fin t ⊕ Fin t) K) * Aunit⁻¹ =
      (spPlaneTorus t ζ (fun i => Multiplicative.ofAdd (φ u i)) :
        GL (Fin t ⊕ Fin t) K) := by
    intro u
    apply Units.ext
    simp only [Units.val_mul, hAval]
    rw [TorC.coe_spPlaneTorus, TorC.coe_spPlaneTorus]
    change A * M u * ((Aunit⁻¹ : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) = M (φ u)
    have h := (hblocks u).1
    have hinv : A * ((Aunit⁻¹ : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) = 1 := by
      rw [← hAval]
      exact Units.mul_inv Aunit
    calc A * M u * ((Aunit⁻¹ : GL (Fin t ⊕ Fin t) K) :
          Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)
        = (A * M u) * ((Aunit⁻¹ : GL (Fin t ⊕ Fin t) K) :
            Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) := by rw [Matrix.mul_assoc]
      _ = (M (φ u) * A) * ((Aunit⁻¹ : GL (Fin t ⊕ Fin t) K) :
            Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) := by rw [h]
      _ = M (φ u) * (A * ((Aunit⁻¹ : GL (Fin t ⊕ Fin t) K) :
            Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)) := by rw [Matrix.mul_assoc]
      _ = M (φ u) := by rw [hinv, Matrix.mul_one]
  have hgA : ∀ f : Fin t → Multiplicative (ZMod 3), ∃ f',
      Aunit * (spPlaneTorus t ζ f : GL (Fin t ⊕ Fin t) K) * Aunit⁻¹ =
        (spPlaneTorus t ζ f' : GL (Fin t ⊕ Fin t) K) := by
    intro f
    refine ⟨fun i => Multiplicative.ofAdd (φ (fun j => Multiplicative.toAdd (f j)) i), ?_⟩
    simpa using hAeq (fun j => Multiplicative.toAdd (f j))
  obtain ⟨π, ε, hε, hπ⟩ := TorC.exists_signedPerm_of_normalizes_gl
    (F := K) (p := 3) Nat.prime_three (by norm_num) hζ Aunit hgA
  refine PlaneRaw.mem_signedPermGroup_of_apply φ π ε hε (fun u i => ?_)
  let f : Fin t → Multiplicative (ZMod 3) := fun j => Multiplicative.ofAdd (u j)
  let f' : Fin t → Multiplicative (ZMod 3) := fun j => Multiplicative.ofAdd (φ u j)
  have h : Aunit * (spPlaneTorus t ζ f : GL (Fin t ⊕ Fin t) K) * Aunit⁻¹ =
      (spPlaneTorus t ζ f' : GL (Fin t ⊕ Fin t) K) := by
    simpa [f, f'] using hAeq u
  simpa [f, f'] using hπ f f' h i

theorem linAmbientTorusAut_holds : LinAmbientTorusAut := by
  intro K _ _ _ ζ t ε hK hζ
  have hsub : torusAut ζ t ε ⊤ ⊆ ((PlaneRaw.signedPermGroup t : Subgroup _) : Set _) :=
    linTorusAutSubsetSignedPerm_holds ζ t ε hK hζ ⊤
  have hsup : ((PlaneRaw.signedPermGroup t : Subgroup _) : Set _) ⊆ torusAut ζ t ε ⊤ :=
    fun φ hφ => mem_torusAut_of_mem_spTorusAut ζ t ε (fun _ _ => Subgroup.mem_top _)
      (SpBlocks.signedPermGroup_subset_torusAut_top (ζ := ζ) hK hζ hφ)
  rw [show PlaneRaw.ambientNormalizer (.linear ε) t = PlaneRaw.signedPermGroup t from rfl]
  exact Set.Subset.antisymm hsub hsup

end CFSG.StandardType.GGQ2Frame.LinBlocks
