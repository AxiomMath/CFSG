module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCenter
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType


private lemma scalarGL_coe {N : ℕ} {K : Type} [Field K] (u : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      (u : K) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private lemma scalarGL_comm {N : ℕ} {K : Type} [Field K] (u : Kˣ) (X : GL (Fin N) K) :
    Matrix.GeneralLinearGroup.scalar (Fin N) u * X =
      X * Matrix.GeneralLinearGroup.scalar (Fin N) u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact Matrix.scalar_comm (↑u) (fun r => Commute.all (↑u) r) (X : Matrix (Fin N) (Fin N) K)

private lemma scalarGL_conj {N : ℕ} {K : Type} [Field K] (u : Kˣ) (X : GL (Fin N) K) :
    Matrix.GeneralLinearGroup.scalar (Fin N) u * X *
      (Matrix.GeneralLinearGroup.scalar (Fin N) u)⁻¹ = X := by
  rw [scalarGL_comm u X, mul_assoc, mul_inv_cancel, mul_one]

private lemma scalarGL_mul_coe {N : ℕ} {K : Type} [Field K] (u : Kˣ) (X : GL (Fin N) K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin N) u * X : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = (u : K) • (X : Matrix (Fin N) (Fin N) K) := by
  rw [Units.val_mul, scalarGL_coe, smul_mul_assoc, one_mul]

private lemma one_ne_zero_matrix {N : ℕ} {K : Type} [Field K] (hN : 1 ≤ N) :
    (1 : Matrix (Fin N) (Fin N) K) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
  simp [Matrix.one_apply] at h00

private lemma unit_ne_zero_of_eq_smul {N : ℕ} {K : Type} [Field K] (hN : 1 ≤ N)
    {X : GL (Fin N) K} {c : K} {B : Matrix (Fin N) (Fin N) K}
    (h : (X : Matrix (Fin N) (Fin N) K) = c • B) : c ≠ 0 := by
  intro hc
  have hX0 : (X : Matrix (Fin N) (Fin N) K) = 0 := by rw [h, hc, zero_smul]
  have h1 : (X : Matrix (Fin N) (Fin N) K) *
      ((X⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hX0, zero_mul] at h1
  exact one_ne_zero_matrix hN h1.symm

private lemma scalarGL_injective {N : ℕ} {K : Type} [Field K] (hN : 1 ≤ N) :
    Function.Injective
      (fun u : Kˣ => (Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K)) := by
  intro u v h
  have h' : ((Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) =
      ((Matrix.GeneralLinearGroup.scalar (Fin N) v : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) := by
    simpa using congrArg (fun Y : GL (Fin N) K => (Y : Matrix (Fin N) (Fin N) K)) h
  rw [scalarGL_coe, scalarGL_coe] at h'
  have h00 := congrFun (congrFun h' ⟨0, by omega⟩) ⟨0, by omega⟩
  simp [Matrix.smul_apply, Matrix.one_apply] at h00
  exact Units.ext h00

private theorem congr_recipeEquiv_graphAut {K : Type} [Field K] {N : ℕ}
    {A : GL (Fin N) K}
    {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = A * h * A⁻¹) φ) :
    MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K) φ = LinearFlag.conjAut N K A := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective N K x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  set h : ↥(LargeEvenSLGroup (Fin N) K) := (CFSG.StandardType.TypeA.slKerEquiv N K).symm g
  have he : (CFSG.StandardType.TypeA.recipeEquiv N K)
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) = LinearFlag.proj N K g := by
    rw [CFSG.StandardType.TypeA.recipeEquiv_mk]
    simp [h]
  have hsymm : (CFSG.StandardType.TypeA.recipeEquiv N K).symm (LinearFlag.proj N K g)
      = LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h := by
    rw [← he, MulEquiv.symm_apply_apply]
  rw [hsymm]
  have hφh : φ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h)
      = LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) ((MulAut.conjNormal A) h) := by
    apply hφ
    rw [MulAut.conjNormal_apply]
  rw [hφh, CFSG.StandardType.TypeA.recipeEquiv_mk, LinearFlag.conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [CFSG.StandardType.TypeA.coe_slConjugation']
  change ((↑((MulAut.conjNormal A) h) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = _
  rw [MulAut.conjNormal_apply]
  simp only [Units.val_mul]
  have hh : ((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = (g : Matrix (Fin N) (Fin N) K) := rfl
  rw [hh]

private theorem exists_unit_smul_of_conjAut_eq {K : Type} [Field K] [Finite K] {N : ℕ}
    (hN : 1 ≤ N)
    {A B : GL (Fin N) K} {φ ψ : MulAut (PSLg N K)}
    (hφ : MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K) φ = LinearFlag.conjAut N K A)
    (hψ : MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K) ψ = LinearFlag.conjAut N K B)
    (hcomm : φ * ψ * φ⁻¹ = ψ) :
    ∃ lam : Kˣ, ((A * B * A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      (lam : K) • (B : Matrix (Fin N) (Fin N) K) := by
  have hM : LinearFlag.conjAut N K (A * B * A⁻¹ * B⁻¹) = 1 := by
    have h2 : LinearFlag.conjAut N K A * LinearFlag.conjAut N K B *
        (LinearFlag.conjAut N K A)⁻¹ = LinearFlag.conjAut N K B := by
      simpa only [map_mul, map_inv, hφ, hψ] using
        congrArg (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K)) hcomm
    calc LinearFlag.conjAut N K (A * B * A⁻¹ * B⁻¹)
        = LinearFlag.conjAut N K A * LinearFlag.conjAut N K B *
            (LinearFlag.conjAut N K A)⁻¹ * (LinearFlag.conjAut N K B)⁻¹ := by
            simp only [map_mul, map_inv]
      _ = LinearFlag.conjAut N K B * (LinearFlag.conjAut N K B)⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel _
  obtain ⟨c, hc⟩ := CFSG.StandardType.TypeA.exists_scalar_of_conjAut_eq_one (d := N) (K := K) hM
  have hc1 : (((A * B * A⁻¹ * B⁻¹ : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) = c • 1 := by
    rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hAB : ((A * B * A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      c • (B : Matrix (Fin N) (Fin N) K) := by
    have h := congrArg (fun T : Matrix (Fin N) (Fin N) K =>
        T * (B : Matrix (Fin N) (Fin N) K)) hc1
    have hL : (((A * B * A⁻¹ * B⁻¹ : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) *
        (B : Matrix (Fin N) (Fin N) K) = ((A * B * A⁻¹ : GL (Fin N) K) :
          Matrix (Fin N) (Fin N) K) := by
      calc (((A * B * A⁻¹ * B⁻¹ : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) *
            (B : Matrix (Fin N) (Fin N) K)
          = (((A * B * A⁻¹ * B⁻¹) * B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
              exact (Units.val_mul (A * B * A⁻¹ * B⁻¹) B).symm
        _ = ((A * B * A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
              congr 1
              group
    rw [hL] at h
    simpa only [smul_mul_assoc, one_mul] using h
  refine ⟨Units.mk0 c (unit_ne_zero_of_eq_smul hN hAB), ?_⟩
  rw [Units.val_mk0, hAB]

private lemma conj_of_conj_scalar {N : ℕ} {K : Type} [Field K] (P Q : GL (Fin N) K) (u : Kˣ)
    (d : GL (Fin N) K)
    (hQ : Q * d * Q⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) u * d) :
    P * (Q * d * Q⁻¹) * P⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin N) u * (P * d * P⁻¹) := by
  rw [hQ]
  rw [show P * (Matrix.GeneralLinearGroup.scalar (Fin N) u * d) * P⁻¹ =
      (P * Matrix.GeneralLinearGroup.scalar (Fin N) u) * d * P⁻¹ from by group]
  rw [← scalarGL_comm u P]
  group

private lemma scalar_of_smul_scalar {N : ℕ} {K : Type} [Field K] (u v : Kˣ)
    (d : GL (Fin N) K) :
    Matrix.GeneralLinearGroup.scalar (Fin N) v *
      (Matrix.GeneralLinearGroup.scalar (Fin N) u * d) =
    Matrix.GeneralLinearGroup.scalar (Fin N) (u * v) * d := by
  rw [← mul_assoc, map_mul]
  rw [scalarGL_comm v (Matrix.GeneralLinearGroup.scalar (Fin N) u)]

theorem linShape_rank_lambda
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {Ā : Subgroup (MulAut (PSLg N K))}
    {δ' : MulAut (PSLg N K)}
    {J' : Subgroup (PSLg N K)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      Set.univ)
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ') :
    ∃ (lam : Ā →* Kˣ) (g : Ā → GL (Fin N) K),
      (∀ a : Ā, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
          (fun h h' => (h' : GL (Fin N) K) = g a * h * (g a)⁻¹) (a : MulAut (PSLg N K))) ∧
      (∀ a : Ā, ((g a * d * (g a)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          (lam a : K) • (d : Matrix (Fin N) (Fin N) K)) ∧
      (∀ a : Ā, (lam a) ^ 3 = 1) := by
  classical
  have hN : 2 ≤ N := by
    by_contra h
    have h1 : N ≤ 1 := by omega
    haveI : Subsingleton (LinearFlag.projectiveSL N K) :=
      CFSG.AGLEmbedding.ToralCensus.subsingleton_projectiveSL h1 K
    haveI : Subsingleton (PSLg N K) :=
      Subsingleton.intro fun x y =>
        (CFSG.StandardType.TypeA.recipeEquiv N K).injective (Subsingleton.elim _ _)
    have hδ : δ' = 1 := by
      apply MulEquiv.ext
      intro x
      exact Subsingleton.elim _ _
    exact hR.ne_one hδ
  have hN1 : 1 ≤ N := by omega
  have hmem : ∀ a : Ā, ∃ A : GL (Fin N) K,
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = A * h * A⁻¹) (a : MulAut (PSLg N K)) := by
    intro a
    simpa only [LargeEvenMatConjImage, Set.mem_setOf_eq, Set.mem_univ, true_and] using
      hĀI (a : MulAut (PSLg N K)) a.2
  choose g hg using hmem
  have hcongr : ∀ a : Ā, (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K))
      (a : MulAut (PSLg N K)) = LinearFlag.conjAut N K (g a) := fun a =>
    congr_recipeEquiv_graphAut (hg a)
  have hd_congr : (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K)) δ' =
      LinearFlag.conjAut N K d := congr_recipeEquiv_graphAut hd
  have hcomm : ∀ a : Ā,
      (a : MulAut (PSLg N K)) * δ' * (a : MulAut (PSLg N K))⁻¹ = δ' := by
    intro a
    have hc := CFSG.Open.IsElemAbelian.comm hR.elem a.2 hR.mem
    rw [hc]
    group
  have hlam_exists : ∀ a : Ā, ∃ lam : Kˣ,
      ((g a * d * (g a)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        (lam : K) • (d : Matrix (Fin N) (Fin N) K) := fun a =>
    exists_unit_smul_of_conjAut_eq hN1 (hcongr a) hd_congr (hcomm a)
  choose lamFun hlamFun using hlam_exists
  have hlam_mul : ∀ a b : Ā, lamFun (a * b) = lamFun a * lamFun b := by
    intro a b
    have hconj_ab : LinearFlag.conjAut N K (g (a * b) * (g a * g b)⁻¹) = 1 := by
      have h1 : (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K))
            ((a * b : Ā) : MulAut (PSLg N K)) =
          (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K))
            (a : MulAut (PSLg N K)) *
          (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K))
            (b : MulAut (PSLg N K)) := by
        have hco : ((a * b : Ā) : MulAut (PSLg N K)) =
            (a : MulAut (PSLg N K)) * (b : MulAut (PSLg N K)) := rfl
        rw [hco, map_mul]
      rw [hcongr (a * b), hcongr a, hcongr b] at h1
      calc LinearFlag.conjAut N K (g (a * b) * (g a * g b)⁻¹)
          = LinearFlag.conjAut N K (g (a * b)) *
              (LinearFlag.conjAut N K (g a * g b))⁻¹ := by rw [map_mul, map_inv]
        _ = (LinearFlag.conjAut N K (g a) * LinearFlag.conjAut N K (g b)) *
              (LinearFlag.conjAut N K (g a) * LinearFlag.conjAut N K (g b))⁻¹ := by
              rw [h1, map_mul]
        _ = 1 := mul_inv_cancel _
    obtain ⟨s, hs⟩ := CFSG.StandardType.TypeA.exists_scalar_of_conjAut_eq_one hconj_ab
    have hs1 : (((g (a * b) * (g a * g b)⁻¹ : GL (Fin N) K)) :
        Matrix (Fin N) (Fin N) K) = s • 1 := by
      rw [hs, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    let S : GL (Fin N) K :=
      Matrix.GeneralLinearGroup.scalar (Fin N) (Units.mk0 s (unit_ne_zero_of_eq_smul hN1 hs1))
    have hS : (S : Matrix (Fin N) (Fin N) K) = s • 1 := by
      rw [show S = Matrix.GeneralLinearGroup.scalar (Fin N)
          (Units.mk0 s (unit_ne_zero_of_eq_smul hN1 hs1)) from rfl, scalarGL_coe, Units.val_mk0]
    have hEq : g (a * b) * (g a * g b)⁻¹ = S := by
      apply Units.ext
      rw [hs1, hS]
    have hgab : g (a * b) = S * (g a * g b) := by
      calc g (a * b) = (g (a * b) * (g a * g b)⁻¹) * (g a * g b) := by group
        _ = S * (g a * g b) := by rw [hEq]
    have hlamGL_a : (g a * d * (g a)⁻¹ : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun a) * d := by
      apply Units.ext
      rw [scalarGL_mul_coe]
      exact hlamFun a
    have hlamGL_b : (g b * d * (g b)⁻¹ : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun b) * d := by
      apply Units.ext
      rw [scalarGL_mul_coe]
      exact hlamFun b
    have hfinal : (g (a * b) * d * (g (a * b))⁻¹ : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun a * lamFun b) * d := by
      calc (g (a * b) * d * (g (a * b))⁻¹ : GL (Fin N) K)
          = S * (g a * g b) * d * (S * (g a * g b))⁻¹ := by rw [hgab]
        _ = S * ((g a * g b) * d * (g a * g b)⁻¹) * S⁻¹ := by
              rw [mul_inv_rev]
              group
        _ = (g a * g b) * d * (g a * g b)⁻¹ := by
              rw [show S = Matrix.GeneralLinearGroup.scalar (Fin N)
                  (Units.mk0 s (unit_ne_zero_of_eq_smul hN1 hs1)) from rfl]
              exact scalarGL_conj _ _
        _ = g a * (g b * d * (g b)⁻¹) * (g a)⁻¹ := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun b) * (g a * d * (g a)⁻¹) :=
              conj_of_conj_scalar (g a) (g b) (lamFun b) d hlamGL_b
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun b) *
              (Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun a) * d) := by rw [hlamGL_a]
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun a * lamFun b) * d :=
              scalar_of_smul_scalar (lamFun a) (lamFun b) d
    have hlamGL_ab : (g (a * b) * d * (g (a * b))⁻¹ : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun (a * b)) * d := by
      apply Units.ext
      rw [scalarGL_mul_coe]
      exact hlamFun (a * b)
    have hT : Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun (a * b)) =
        Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun a * lamFun b) := by
      have h' : Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun (a * b)) * d =
          Matrix.GeneralLinearGroup.scalar (Fin N) (lamFun a * lamFun b) * d :=
        hlamGL_ab.symm.trans hfinal
      exact mul_right_cancel h'
    exact scalarGL_injective hN1 hT
  let lam : Ā →* Kˣ := MonoidHom.mk' lamFun hlam_mul
  have hlam_apply : ∀ a : Ā, lam a = lamFun a := fun a => rfl
  refine ⟨lam, g, hg, ?_, ?_⟩
  · intro a
    rw [hlam_apply]
    exact hlamFun a
  · intro a
    have ha3 : a ^ 3 = 1 := by
      apply Subtype.ext
      show ((a : MulAut (PSLg N K)) ^ 3) = (1 : MulAut (PSLg N K))
      exact hR.elem.2 (a : MulAut (PSLg N K)) a.2
    calc (lam a) ^ 3 = lam (a ^ 3) := by rw [map_pow]
      _ = lam 1 := by rw [ha3]
      _ = 1 := map_one lam


end

end CFSG.StandardType.TablePThreeKG

end
