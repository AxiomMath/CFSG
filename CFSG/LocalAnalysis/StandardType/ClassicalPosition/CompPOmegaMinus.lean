module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.Open.MatrixModelCore
public import CFSG.LieType.Universal.Spin.Roots
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private lemma cpOm_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma cpOm_dotProduct_mulVec_transpose {ι F : Type} [Fintype ι] [CommSemiring F]
    (M : Matrix ι ι F) (x y : ι → F) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

private lemma cpOm_formAdj_id {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G a : Matrix ι ι F) : formAdj (RingHom.id F) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id F)) = a from by ext i j; rfl]

private lemma cpOm_formAdj_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G a : Matrix ι ι F} (hG : IsUnit G.det) (y : ι → F) :
    G.mulVec ((formAdj (RingHom.id F) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [cpOm_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

private lemma cpOm_formAdj_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    (a : Matrix ι ι F) (x y : ι → F) :
    QuadraticMap.polar Q (a.mulVec x) y =
      QuadraticMap.polar Q x ((formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) a).mulVec y) := by
  rw [cpOm_polar_eq_dot Q, cpOm_polar_eq_dot Q,
    cpOm_dotProduct_mulVec_transpose a x
      ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y),
    cpOm_formAdj_mulVec hG y]

private lemma cpOm_isUnit_det {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hnd))

private lemma cpOm_isometry_of_quad {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (M : Matrix ι ι F)
    (hM : ∀ x : ι → F, Q (M.mulVec x) = Q x) :
    M.transpose * LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * M =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  have hpol : ∀ x y, QuadraticMap.polar Q (M.mulVec x) (M.mulVec y) =
      QuadraticMap.polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← cpOm_polar_eq_dot Q (M.mulVec x) (M.mulVec y),
    ← cpOm_polar_eq_dot Q x y]
  exact hpol x y

private lemma cpOm_blk_mul_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (a : GL ι F) (ε : Matrix ι ι F) (hε : IsIdempotentElem ε)
    (hcomm : (a : Matrix ι ι F) * ε = ε * (a : Matrix ι ι F)) :
    ((a : Matrix ι ι F) * ε + (1 - ε)) *
      (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε)) = 1 := by
  have hqε : (1 - ε) * ε = 0 := IsIdempotentElem.one_sub_mul_self hε
  have hεq : ε * (1 - ε) = 0 := IsIdempotentElem.mul_one_sub_self hε
  have hqq : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [mul_sub, mul_one, hqε, sub_zero]
  have hcommInv : ((a⁻¹ : GL ι F) : Matrix ι ι F) * ε = ε * a⁻¹ := by
    have hc : Commute (a : Matrix ι ι F) ε := hcomm
    exact hc.units_inv_left.eq
  have hainvq : ((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε) = (1 - ε) * a⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcommInv]
  have haa : (a : Matrix ι ι F) * ((a⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((a : Matrix ι ι F) * ε) * (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε) = ε := by
    calc ((a : Matrix ι ι F) * ε) * (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε)
        = (a : Matrix ι ι F) * (ε * (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε)) := by
          rw [Matrix.mul_assoc]
      _ = (a : Matrix ι ι F) * ((ε * ((a⁻¹ : GL ι F) : Matrix ι ι F)) * ε) := by
          rw [Matrix.mul_assoc]
      _ = (a : Matrix ι ι F) * ((((a⁻¹ : GL ι F) : Matrix ι ι F) * ε) * ε) := by
          rw [hcommInv]
      _ = (a : Matrix ι ι F) * (((a⁻¹ : GL ι F) : Matrix ι ι F) * (ε * ε)) := by
          rw [Matrix.mul_assoc]
      _ = (a : Matrix ι ι F) * (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε) := by
          rw [hε]
      _ = ((a : Matrix ι ι F) * ((a⁻¹ : GL ι F) : Matrix ι ι F)) * ε := by
          rw [← Matrix.mul_assoc]
      _ = ε := by rw [haa, one_mul]
  have h2 : ((a : Matrix ι ι F) * ε) * (1 - ε) = 0 := by
    rw [Matrix.mul_assoc, hεq, mul_zero]
  have h3 : (1 - ε) * (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε) = 0 := by
    calc (1 - ε) * (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε)
        = ((1 - ε) * ((a⁻¹ : GL ι F) : Matrix ι ι F)) * ε := by
          rw [← Matrix.mul_assoc]
      _ = (((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε)) * ε := by
          rw [hainvq.symm]
      _ = ((a⁻¹ : GL ι F) : Matrix ι ι F) * ((1 - ε) * ε) := by
          rw [Matrix.mul_assoc]
      _ = 0 := by rw [hqε, mul_zero]
  rw [add_mul, mul_add, mul_add]
  rw [h1, h2, h3, hqq]
  abel

private noncomputable def cpOm_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (a : GL ι F) (ε : Matrix ι ι F) (hε : IsIdempotentElem ε)
    (hcomm : (a : Matrix ι ι F) * ε = ε * (a : Matrix ι ι F)) : GL ι F :=
  Units.mkOfMulEqOne ((a : Matrix ι ι F) * ε + (1 - ε))
    (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε))
    (cpOm_blk_mul_inv a ε hε hcomm)

private lemma cpOm_blk_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (a : GL ι F) (ε : Matrix ι ι F) (hε : IsIdempotentElem ε)
    (hcomm : (a : Matrix ι ι F) * ε = ε * (a : Matrix ι ι F)) :
    ((cpOm_blk a ε hε hcomm : GL ι F) : Matrix ι ι F) =
      (a : Matrix ι ι F) * ε + (1 - ε) :=
  Units.val_mkOfMulEqOne (cpOm_blk_mul_inv a ε hε hcomm)

private lemma cpOm_quad_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {ε : Matrix ι ι F} (hε : IsIdempotentElem ε)
    (hst : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) ε = ε)
    {a : GL ι F} (ha : ∀ v, Q ((a : Matrix ι ι F).mulVec v) = Q v)
    (hcomm : (a : Matrix ι ι F) * ε = ε * (a : Matrix ι ι F)) :
    ∀ v, Q (((cpOm_blk a ε hε hcomm : GL ι F) : Matrix ι ι F).mulVec v) = Q v := by
  have hcommInv : ((a⁻¹ : GL ι F) : Matrix ι ι F) * ε = ε * a⁻¹ := by
    have hc : Commute (a : Matrix ι ι F) ε := hcomm
    exact hc.units_inv_left.eq
  have hiso : Matrix.transpose (((a : Matrix ι ι F).map (RingHom.id F))) *
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * (a : Matrix ι ι F) =
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
    rw [show (a : Matrix ι ι F).map (RingHom.id F) = (a : Matrix ι ι F) from by
      ext i j; rfl]
    exact cpOm_isometry_of_quad Q (a : Matrix ι ι F) ha
  have hAdj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) (a : Matrix ι ι F) =
      ((a⁻¹ : GL ι F) : Matrix ι ι F) :=
    Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG a hiso
  intro v
  have hpolar : QuadraticMap.polar Q ((a : Matrix ι ι F).mulVec (ε.mulVec v))
      ((1 - ε).mulVec v) = 0 := by
    calc QuadraticMap.polar Q ((a : Matrix ι ι F).mulVec (ε.mulVec v)) ((1 - ε).mulVec v)
        = QuadraticMap.polar Q (ε.mulVec v)
            ((formAdj (RingHom.id F)
              (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) (a : Matrix ι ι F)).mulVec
              ((1 - ε).mulVec v)) := by
          rw [cpOm_formAdj_apply Q hG (a : Matrix ι ι F) (ε.mulVec v) ((1 - ε).mulVec v)]
      _ = QuadraticMap.polar Q (ε.mulVec v)
            (((a⁻¹ : GL ι F) : Matrix ι ι F).mulVec ((1 - ε).mulVec v)) := by rw [hAdj]
      _ = QuadraticMap.polar Q v
            (ε.mulVec (((a⁻¹ : GL ι F) : Matrix ι ι F).mulVec ((1 - ε).mulVec v))) := by
          rw [cpOm_formAdj_apply Q hG ε v
            (((a⁻¹ : GL ι F) : Matrix ι ι F).mulVec ((1 - ε).mulVec v)), hst]
      _ = QuadraticMap.polar Q v
            ((ε * ((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε)).mulVec v) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by
          have hzero : ε * ((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε) = 0 := by
            calc ε * ((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - ε)
                = (((a⁻¹ : GL ι F) : Matrix ι ι F) * ε) * (1 - ε) := by
                  rw [hcommInv.symm]
              _ = ((a⁻¹ : GL ι F) : Matrix ι ι F) * (ε * (1 - ε)) := by
                  rw [Matrix.mul_assoc]
              _ = 0 := by rw [IsIdempotentElem.mul_one_sub_self hε, mul_zero]
          rw [hzero, Matrix.zero_mulVec, QuadraticMap.polar_zero_right]
  have hpε1 : QuadraticMap.polar Q (ε.mulVec v) ((1 - ε).mulVec v) = 0 := by
    calc QuadraticMap.polar Q (ε.mulVec v) ((1 - ε).mulVec v)
        = QuadraticMap.polar Q v
            ((formAdj (RingHom.id F)
              (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) ε).mulVec
              ((1 - ε).mulVec v)) := by
          rw [cpOm_formAdj_apply Q hG ε v ((1 - ε).mulVec v)]
      _ = QuadraticMap.polar Q v (ε.mulVec ((1 - ε).mulVec v)) := by rw [hst]
      _ = QuadraticMap.polar Q v ((ε * (1 - ε)).mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [IsIdempotentElem.mul_one_sub_self hε, Matrix.zero_mulVec,
            QuadraticMap.polar_zero_right]
  have hXv : ((cpOm_blk a ε hε hcomm : GL ι F) : Matrix ι ι F).mulVec v =
      (a : Matrix ι ι F).mulVec (ε.mulVec v) + (1 - ε).mulVec v := by
    rw [cpOm_blk_val, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [hXv]
  calc Q ((a : Matrix ι ι F).mulVec (ε.mulVec v) + (1 - ε).mulVec v)
      = Q ((a : Matrix ι ι F).mulVec (ε.mulVec v)) + Q ((1 - ε).mulVec v) +
        QuadraticMap.polar Q ((a : Matrix ι ι F).mulVec (ε.mulVec v)) ((1 - ε).mulVec v) :=
        QuadraticMap.map_add Q _ _
    _ = Q (ε.mulVec v) + Q ((1 - ε).mulVec v) + 0 := by rw [ha, hpolar, add_zero]
    _ = Q (ε.mulVec v) + Q ((1 - ε).mulVec v) := by rw [add_zero]
    _ = Q (ε.mulVec v + (1 - ε).mulVec v) := by
        rw [QuadraticMap.map_add Q (ε.mulVec v) ((1 - ε).mulVec v), hpε1, add_zero]
    _ = Q v := by
        rw [show ε.mulVec v + (1 - ε).mulVec v = v from by
          rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]]

theorem exists_isComponentOf_glBlockCentralizer_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq))}
    (hJ : IsComponentOf J'
      ((Subgroup.centralizer S).comap (Spin.spinMatrix (Spin.quadMinus n F bq cq)))) :
    ∃ ε, IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' S)) ε ∧
      IsComponentOf J'
        ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε, glBlockCentralizer
        (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε⁆ := by
  classical
  let Q := Spin.quadMinus n F bq cq
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  let A := Algebra.adjoin F (Units.val '' S)
  have hG : IsUnit G.det :=
    cpOm_isUnit_det Q (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr)
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hker : (Spin.spinMatrix Q).ker = ⊥ :=
    Spin.ker_spinMatrix_quadMinus_eq_bot hirr h2
  have hj : Function.Injective (Spin.spinMatrix Q) :=
    (MonoidHom.ker_eq_bot_iff (Spin.spinMatrix Q)).mp hker
  have hblock : ∀ ε ∈ Algebra.adjoin F (Units.val '' S), IsIdempotentElem ε →
      formAdj (RingHom.id F) G ε = ε →
      ∀ x ∈ (Subgroup.centralizer S).comap (Spin.spinMatrix Q),
        ∀ y ∈ (Subgroup.centralizer S).comap (Spin.spinMatrix Q),
        ∃ w : ↥(spinGroup Q),
          (Spin.spinMatrix Q w : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
              (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
            ((((Spin.spinMatrix Q x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
                Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
                  (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε)) *
             (((Spin.spinMatrix Q y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
                Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
                  (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε))) =
            (((Spin.spinMatrix Q y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
                Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
                  (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε)) *
             (((Spin.spinMatrix Q x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
                Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
                  (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε)) := by
    intro ε hεA hid hst x hx y hy
    have hxcomm : ∀ b ∈ Units.val '' S, Commute
        ((Spin.spinMatrix Q x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) b := by
      rintro b ⟨s, hs, rfl⟩
      have hxmem : Spin.spinMatrix Q x ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hx
      have h : ((Spin.spinMatrix Q x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * (s : Matrix _ _ F) =
          (s : Matrix _ _ F) * ((Spin.spinMatrix Q x : GL
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : Matrix _ _ F) := by
        simpa only [Units.val_mul] using
          congrArg Units.val (Subgroup.mem_centralizer_iff.mp hxmem s hs).symm
      exact h
    have hycomm : ∀ b ∈ Units.val '' S, Commute
        ((Spin.spinMatrix Q y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) b := by
      rintro b ⟨s, hs, rfl⟩
      have hymem : Spin.spinMatrix Q y ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hy
      have h : ((Spin.spinMatrix Q y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * (s : Matrix _ _ F) =
          (s : Matrix _ _ F) * ((Spin.spinMatrix Q y : GL
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : Matrix _ _ F) := by
        simpa only [Units.val_mul] using
          congrArg Units.val (Subgroup.mem_centralizer_iff.mp hymem s hs).symm
      exact h
    have hxε : Commute
        ((Spin.spinMatrix Q x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ε :=
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute hεA hxcomm
    have hyε : Commute
        ((Spin.spinMatrix Q y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ε :=
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute hεA hycomm
    let X : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
      cpOm_blk (Spin.spinMatrix Q x) ε hid hxε.eq
    let Y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
      cpOm_blk (Spin.spinMatrix Q y) ε hid hyε.eq
    have hXval : (X : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
        ((Spin.spinMatrix Q x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε) :=
      cpOm_blk_val _ _ _ _
    have hYval : (Y : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
        ((Spin.spinMatrix Q y : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε) :=
      cpOm_blk_val _ _ _ _
    have hXiso : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
        Q ((X : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).mulVec v) = Q v :=
      cpOm_quad_blk Q hG hid hst
        (Spin.spinMatrix_mem Q x) hxε.eq
    have hYiso : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
        Q ((Y : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).mulVec v) = Q v :=
      cpOm_quad_blk Q hG hid hst
        (Spin.spinMatrix_mem Q y) hyε.eq
    have hXcore : X ∈ CFSG.MatrixModel.isometryCore ⇑Q := by
      rw [CFSG.MatrixModel.isometryCore]
      exact Subgroup.subset_closure hXiso
    have hYcore : Y ∈ CFSG.MatrixModel.isometryCore ⇑Q := by
      rw [CFSG.MatrixModel.isometryCore]
      exact Subgroup.subset_closure hYiso
    letI : Bracket (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
        (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) := commutatorElement
    have hcommut : ⁅Y, X⁆ ∈ CFSG.Open.StatedOmega ⇑Q := by
      change ⁅Y, X⁆ ∈
        ⁅CFSG.MatrixModel.isometryCore ⇑Q, CFSG.MatrixModel.isometryCore ⇑Q⁆
      exact Subgroup.commutator_mem_commutator hYcore hXcore
    have hRange : (Spin.spinMatrix Q).range = CFSG.Open.StatedOmega ⇑Q := by
      have h := Spin.range_spinMatrix_quadMinus (n := n) (K := F) (b := bq) (c := cq) hn hirr
      rwa [← Spin.coe_quadMinus n F bq cq] at h
    have hmem : ⁅Y, X⁆ ∈ (Spin.spinMatrix Q).range := by rwa [hRange]
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hmem
    have hprod : ⁅Y, X⁆ * (X * Y) = Y * X := by
      rw [commutatorElement_def]
      group
    refine ⟨w, ?_⟩
    rw [← hXval, ← hYval]
    calc
      (Spin.spinMatrix Q w : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
          ((X : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
           (Y : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))
          = ((⁅Y, X⁆ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
              Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
                (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
            ((X : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
              (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
             (Y : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
              (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) := by rw [hw]
      _ = (Y : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *
          (X : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) := by
          simpa only [Units.val_mul] using congrArg Units.val hprod
  have hone : formAdj (RingHom.id F) G 1 = 1 := Geo.formAdj_one (RingHom.id F) hG
  have hadd : ∀ a ∈ A, ∀ b ∈ A,
      formAdj (RingHom.id F) G (a + b) =
        formAdj (RingHom.id F) G a + formAdj (RingHom.id F) G b :=
    fun a _ b _ => Geo.formAdj_add (RingHom.id F) G a b
  obtain ⟨ε, hεprim, hεcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
      (U := ↥(spinGroup Q)) (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (F := F)
      (Spin.spinMatrix Q) hj S hS (formAdj (RingHom.id F) G) hone hadd hblock hJ
  refine ⟨ε, ?_, hεcomp⟩
  exact (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id F) G A ε).mp hεprim

end CFSG.StandardType.ClassicalPosition
