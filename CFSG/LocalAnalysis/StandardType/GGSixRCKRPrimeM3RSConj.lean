module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSDefs
public import Mathlib.RingTheory.Adjoin.Basic

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma rckConj_stable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : Matrix ι ι F} {M : Matrix ι ι F} (hMe : M * e = e * M) :
    ∀ w : LinearMap.range (Matrix.mulVecLin e),
      M.mulVec (w : ι → F) ∈ LinearMap.range (Matrix.mulVecLin e) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, rfl⟩ := hz
  refine ⟨M.mulVec y, ?_⟩
  show e.mulVec (M.mulVec y) = M.mulVec (e.mulVec y)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMe]

private noncomputable def rckConj_restrict {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {e : Matrix ι ι F}
    {K : Type} [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    {π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K}
    (hπ : RCKBlockCoord S e K π)
    {M : Matrix ι ι F}
    (hMW : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      M.mulVec (w : ι → F) ∈ LinearMap.range (Matrix.mulVecLin e))
    (hMcomm : ∀ a ∈ Algebra.adjoin F (Units.val '' S), Commute M a) :
    (LinearMap.range (Matrix.mulVecLin e)) →ₗ[K]
      (LinearMap.range (Matrix.mulVecLin e)) where
  toFun w := ⟨M.mulVec (w : ι → F), hMW w⟩
  map_add' w₁ w₂ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Matrix.mulVec_add]
  map_smul' κ w := by
    obtain ⟨a, ha⟩ := hπ.1 κ
    apply Subtype.ext
    have h1 : ((κ • w : LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
        (a : Matrix ι ι F).mulVec (w : ι → F) := by
      rw [← ha]
      exact hπ.2.1 a w
    have h2 : ((κ • (⟨M.mulVec (w : ι → F), hMW w⟩ :
          LinearMap.range (Matrix.mulVecLin e)) :
          LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
        (a : Matrix ι ι F).mulVec (M.mulVec (w : ι → F)) := by
      rw [← ha]
      exact hπ.2.1 a ⟨M.mulVec (w : ι → F), hMW w⟩
    change M.mulVec ((κ • w : LinearMap.range (Matrix.mulVecLin e)) : ι → F) =
      ((κ • (⟨M.mulVec (w : ι → F), hMW w⟩ : LinearMap.range (Matrix.mulVecLin e)) :
        LinearMap.range (Matrix.mulVecLin e)) : ι → F)
    rw [h1, h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hMcomm a a.2).eq]

theorem rckBlockRSMat_conj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {k : ℕ} {S : Set (GL ι F)} {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {K : Type} [Field K] [Algebra F K]
    [Module K (LinearMap.range (Matrix.mulVecLin e))]
    [IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e))]
    {π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K}
    (hπ : RCKBlockCoord S e K π)
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)))
    (s' : GL ι F) (hs' : ∀ s ∈ S, Commute s' s) :
    ∃ t₀ : GL (Fin (k + 1)) K, ∀ x : Matrix (Fin (k + 1)) (Fin (k + 1)) K,
      rckBlockRSMat b ((t₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) K) * x *
          ((t₀⁻¹ : GL (Fin (k + 1)) K) : Matrix (Fin (k + 1)) (Fin (k + 1)) K)) =
        (s' : Matrix ι ι F) * rckBlockRSMat b x *
          ((s'⁻¹ : GL ι F) : Matrix ι ι F) := by
  classical
  let M : Matrix ι ι F := s'
  let Mi : Matrix ι ι F := ((s'⁻¹ : GL ι F) : Matrix ι ι F)
  have hgen : ∀ b ∈ (Units.val '' S : Set (Matrix ι ι F)), Commute M b := by
    rintro b ⟨s, hs, rfl⟩
    exact (hs' s hs).units_val
  have hMcomm : ∀ a ∈ Algebra.adjoin F (Units.val '' S), Commute M a :=
    fun a ha => Algebra.commute_of_mem_adjoin_of_forall_mem_commute (a := M) ha hgen
  have hMe : M * e = e * M := (hMcomm e he.1).eq
  have hgeni : ∀ b ∈ (Units.val '' S : Set (Matrix ι ι F)), Commute Mi b := by
    rintro b ⟨s, hs, rfl⟩
    exact (hs' s hs).inv_left.units_val
  have hMicomm : ∀ a ∈ Algebra.adjoin F (Units.val '' S), Commute Mi a :=
    fun a ha => Algebra.commute_of_mem_adjoin_of_forall_mem_commute (a := Mi) ha hgeni
  have hMie : Mi * e = e * Mi := (hMicomm e he.1).eq
  let u : (LinearMap.range (Matrix.mulVecLin e)) →ₗ[K]
      (LinearMap.range (Matrix.mulVecLin e)) :=
    rckConj_restrict hπ (rckConj_stable hMe) hMcomm
  let uI : (LinearMap.range (Matrix.mulVecLin e)) →ₗ[K]
      (LinearMap.range (Matrix.mulVecLin e)) :=
    rckConj_restrict hπ (rckConj_stable hMie) hMicomm
  have hu_apply : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      (u w : ι → F) = M.mulVec (w : ι → F) := fun _ => rfl
  have huI_apply : ∀ w : LinearMap.range (Matrix.mulVecLin e),
      (uI w : ι → F) = Mi.mulVec (w : ι → F) := fun _ => rfl
  have hMMi : M * Mi = 1 := by
    change (s' : Matrix ι ι F) * ((s'⁻¹ : GL ι F) : Matrix ι ι F) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by
    change ((s'⁻¹ : GL ι F) : Matrix ι ι F) * (s' : Matrix ι ι F) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have huv : u.comp uI = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change M.mulVec (Mi.mulVec (w : ι → F)) = (w : ι → F)
    rw [Matrix.mulVec_mulVec, hMMi, Matrix.one_mulVec]
  have hvu : uI.comp u = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change Mi.mulVec (M.mulVec (w : ι → F)) = (w : ι → F)
    rw [Matrix.mulVec_mulVec, hMiM, Matrix.one_mulVec]
  let U : Matrix (Fin (k + 1)) (Fin (k + 1)) K := LinearMap.toMatrix b b u
  let UI : Matrix (Fin (k + 1)) (Fin (k + 1)) K := LinearMap.toMatrix b b uI
  have hU_mul : U * UI = 1 := by
    change LinearMap.toMatrix b b u * LinearMap.toMatrix b b uI = 1
    rw [← LinearMap.toMatrix_comp b b b, huv, LinearMap.toMatrix_id]
  have hUI_mul : UI * U = 1 := by
    change LinearMap.toMatrix b b uI * LinearMap.toMatrix b b u = 1
    rw [← LinearMap.toMatrix_comp b b b, hvu, LinearMap.toMatrix_id]
  let t₀ : GL (Fin (k + 1)) K := Units.mk U UI hU_mul hUI_mul
  have ht₀ : ((t₀ : GL (Fin (k + 1)) K) : Matrix (Fin (k + 1)) (Fin (k + 1)) K) = U := rfl
  have ht₀i : ((t₀⁻¹ : GL (Fin (k + 1)) K) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) K) = UI := rfl
  refine ⟨t₀, ?_⟩
  intro x
  rw [ht₀, ht₀i]
  have hL : ∀ (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (v : ι → F),
      Matrix.toLin' (rckBlockRSMat b y) v =
        (v - Matrix.mulVecLin e v) +
          ((Matrix.toLin b b y) ((Matrix.mulVecLin e).rangeRestrict v) : ι → F) := by
    intro y v
    rw [rckBlockRSMat, Matrix.toLin'_toMatrix']
    rfl
  have hLmulVec : ∀ (y : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (v : ι → F),
      (rckBlockRSMat b y).mulVec v =
        (v - Matrix.mulVecLin e v) +
          ((Matrix.toLin b b y) ((Matrix.mulVecLin e).rangeRestrict v) : ι → F) := by
    intro y v
    rw [← Matrix.toLin'_apply, hL y v]
  have hAMi : ∀ v : ι → F,
      Matrix.mulVecLin e (Mi.mulVec v) = Mi.mulVec (Matrix.mulVecLin e v) := by
    intro v
    show e.mulVec (Mi.mulVec v) = Mi.mulVec (e.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMie]
  have huI_rr : ∀ v : ι → F,
      uI ((Matrix.mulVecLin e).rangeRestrict v) =
        (Matrix.mulVecLin e).rangeRestrict (Mi.mulVec v) := by
    intro v
    apply Subtype.ext
    change Mi.mulVec (Matrix.mulVecLin e v) = Matrix.mulVecLin e (Mi.mulVec v)
    exact (hAMi v).symm
  have hkey : ∀ v : ι → F,
      (Matrix.toLin b b (U * x * UI)) ((Matrix.mulVecLin e).rangeRestrict v) =
        u ((Matrix.toLin b b x) ((Matrix.mulVecLin e).rangeRestrict (Mi.mulVec v))) := by
    intro v
    have hlin : Matrix.toLin b b (U * x * UI) =
        u.comp ((Matrix.toLin b b x).comp uI) := by
      rw [Matrix.toLin_mul b b b, Matrix.toLin_mul b b b, Matrix.toLin_toMatrix,
        Matrix.toLin_toMatrix]
      rw [LinearMap.comp_assoc]
    rw [hlin, LinearMap.comp_apply, LinearMap.comp_apply, huI_rr v]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  rw [hL (U * x * UI) w]
  have hRhs : Matrix.toLin' (M * rckBlockRSMat b x * Mi) w =
      M.mulVec ((rckBlockRSMat b x).mulVec (Mi.mulVec w)) := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
  rw [hRhs, hLmulVec x (Mi.mulVec w), hAMi w]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMMi,
    Matrix.one_mulVec]
  rw [add_right_inj, hkey w, hu_apply]

end CFSG.StandardType.RCKRP
