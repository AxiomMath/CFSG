module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.Spin.Roots
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private lemma cpOp_isUnit_det {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hnd))

private lemma cpOp_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma cpOp_formAdj_id {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G a : Matrix ι ι F) : formAdj (RingHom.id F) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id F)) = a from by ext i j; rfl]

private lemma cpOp_formAdj_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G a : Matrix ι ι F} (hG : IsUnit G.det) (y : ι → F) :
    G.mulVec ((formAdj (RingHom.id F) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [cpOp_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

private lemma cpOp_dotProduct_mulVec_transpose {ι F : Type} [Fintype ι] [CommSemiring F]
    (M : Matrix ι ι F) (x y : ι → F) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

private lemma cpOp_formAdj_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    (a : Matrix ι ι F) (x y : ι → F) :
    QuadraticMap.polar Q (a.mulVec x) y =
      QuadraticMap.polar Q x ((formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) a).mulVec y) := by
  rw [cpOp_polar_eq_dot Q, cpOp_polar_eq_dot Q,
    cpOp_dotProduct_mulVec_transpose a x
      ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y),
    cpOp_formAdj_mulVec hG y]

private lemma cpOp_polar_selfAdjoint {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {E : Matrix ι ι F}
    (hE : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) E = E) (x y : ι → F) :
    QuadraticMap.polar Q (E.mulVec x) y = QuadraticMap.polar Q x (E.mulVec y) := by
  rw [cpOp_formAdj_apply Q hG E x y, hE]

private def cpOp_isoGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) : Subgroup (GL ι F) where
  carrier := {g | ∀ v, Q (((g : Matrix ι ι F)).mulVec v) = Q v}
  mul_mem' {a b} ha hb := by
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha := by
    intro v
    have h1 : Q (((a : GL ι F) : Matrix ι ι F).mulVec
        (((a⁻¹ : GL ι F) : Matrix ι ι F).mulVec v)) = Q v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have h2 := ha (((a⁻¹ : GL ι F) : Matrix ι ι F).mulVec v)
    exact h2.symm.trans h1

private lemma cpOp_isometry_of_mem_closure {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (Q : QuadraticForm F (ι → F)) {g : GL ι F}
    (hg : g ∈ Subgroup.closure {A : GL ι F | ∀ v, Q ((A : Matrix ι ι F).mulVec v) = Q v}) :
    ∀ v, Q ((g : Matrix ι ι F).mulVec v) = Q v :=
  (Subgroup.closure_le (cpOp_isoGroup Q)).mpr (fun _ hx => hx) hg

private lemma cpOp_inv_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A B E : Matrix ι ι F} (hAE : A * E = E * A) (hAB : A * B = 1)
    (hBA : B * A = 1) : B * E = E * B := by
  have h : B * E * A = E := by
    calc B * E * A = B * (E * A) := by rw [Matrix.mul_assoc]
      _ = B * (A * E) := by rw [← hAE]
      _ = (B * A) * E := by rw [← Matrix.mul_assoc]
      _ = E := by rw [hBA, Matrix.one_mul]
  calc B * E = B * E * 1 := by rw [Matrix.mul_one]
    _ = B * E * (A * B) := by rw [hAB]
    _ = (B * E * A) * B := by rw [← Matrix.mul_assoc]
    _ = E * B := by rw [h]

private lemma cpOp_blk_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A B E : Matrix ι ι F} (hE : E * E = E) (hAB : A * B = 1)
    (hBE : B * E = E * B) :
    (A * E + (1 - E)) * (B * E + (1 - E)) = 1 := by
  have hAEBE : A * E * (B * E) = E := by
    calc A * E * (B * E)
        = A * (E * (B * E)) := by rw [Matrix.mul_assoc]
      _ = A * ((E * B) * E) := by rw [← Matrix.mul_assoc E B E]
      _ = A * ((B * E) * E) := by rw [← hBE]
      _ = A * (B * (E * E)) := by rw [Matrix.mul_assoc B E E]
      _ = A * (B * E) := by rw [hE]
      _ = (A * B) * E := by rw [← Matrix.mul_assoc A B E]
      _ = E := by rw [hAB, Matrix.one_mul]
  have hAE1 : A * E * (1 - E) = 0 := by
    calc A * E * (1 - E)
        = A * (E * (1 - E)) := by rw [Matrix.mul_assoc]
      _ = A * (E * 1 - E * E) := by rw [Matrix.mul_sub]
      _ = A * (E - E) := by rw [Matrix.mul_one, hE]
      _ = 0 := by rw [sub_self, Matrix.mul_zero]
  have h1EBE : (1 - E) * (B * E) = 0 := by
    calc (1 - E) * (B * E)
        = 1 * (B * E) - E * (B * E) := by rw [Matrix.sub_mul]
      _ = B * E - E * (B * E) := by rw [Matrix.one_mul]
      _ = B * E - B * (E * E) := by
            rw [← Matrix.mul_assoc E B E, ← hBE, Matrix.mul_assoc B E E]
      _ = B * E - B * E := by rw [hE]
      _ = 0 := sub_self _
  have h1E1 : (1 - E) * (1 - E) = 1 - E := by
    calc (1 - E) * (1 - E)
        = 1 * (1 - E) - E * (1 - E) := by rw [Matrix.sub_mul]
      _ = (1 - E) - (E - E * E) := by
            rw [Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
      _ = (1 - E) - (E - E) := by rw [hE]
      _ = 1 - E := by rw [sub_self, sub_zero]
  calc (A * E + (1 - E)) * (B * E + (1 - E))
      = A * E * (B * E) + A * E * (1 - E) +
          ((1 - E) * (B * E) + (1 - E) * (1 - E)) := by
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    _ = E + 0 + (0 + (1 - E)) := by rw [hAEBE, hAE1, h1EBE, h1E1]
    _ = 1 := by abel

private noncomputable def cpOp_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : GL ι F) (E : Matrix ι ι F) (hEid : IsIdempotentElem E)
    (hAE : (A : Matrix ι ι F) * E = E * (A : Matrix ι ι F)) : GL ι F :=
  { val := (A : Matrix ι ι F) * E + (1 - E)
    inv := ((A⁻¹ : GL ι F) : Matrix ι ι F) * E + (1 - E)
    val_inv := by
      have hAB : (A : Matrix ι ι F) * ((A⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hBA : ((A⁻¹ : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hBE : ((A⁻¹ : GL ι F) : Matrix ι ι F) * E =
          E * ((A⁻¹ : GL ι F) : Matrix ι ι F) := cpOp_inv_comm hAE hAB hBA
      exact cpOp_blk_mul hEid hAB hBE
    inv_val := by
      have hAB : (A : Matrix ι ι F) * ((A⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hBA : ((A⁻¹ : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hBE : ((A⁻¹ : GL ι F) : Matrix ι ι F) * E =
          E * ((A⁻¹ : GL ι F) : Matrix ι ι F) := cpOp_inv_comm hAE hAB hBA
      exact cpOp_blk_mul hEid hBA hAE }

private lemma cpOp_blk_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {E A : Matrix ι ι F} (hEid : IsIdempotentElem E)
    (hEadj : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) E = E)
    (hAE : A * E = E * A) (hAiso : ∀ v, Q (A.mulVec v) = Q v) :
    ∀ v, Q ((A * E + (1 - E)).mulVec v) = Q v := by
  intro v
  have hE1 : E * (1 - E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hEid, sub_self]
  have hE1mul : E.mulVec ((1 - E).mulVec v) = 0 := by
    rw [Matrix.mulVec_mulVec, hE1, Matrix.zero_mulVec]
  have hsplit1 : (1 - E).mulVec v = v - E.mulVec v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hX : (A * E + (1 - E)).mulVec v =
      A.mulVec (E.mulVec v) + (1 - E).mulVec v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  rw [hX, QuadraticMap.map_add (⇑Q)]
  have hQA : Q (A.mulVec (E.mulVec v)) = Q (E.mulVec v) := hAiso _
  have hpolar : QuadraticMap.polar Q (A.mulVec (E.mulVec v)) ((1 - E).mulVec v) = 0 := by
    have hAu : A.mulVec (E.mulVec v) = E.mulVec (A.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAE]
    rw [hAu, cpOp_polar_selfAdjoint Q hG hEadj (A.mulVec v) ((1 - E).mulVec v),
      hE1mul]
    exact QuadraticMap.polar_zero_right Q (A.mulVec v)
  have hQv : Q v = Q (E.mulVec v) + Q ((1 - E).mulVec v) := by
    have hvs : v = E.mulVec v + (1 - E).mulVec v := by
      rw [hsplit1]
      abel
    conv_lhs => rw [hvs]
    rw [QuadraticMap.map_add (⇑Q),
      cpOp_polar_selfAdjoint Q hG hEadj v ((1 - E).mulVec v), hE1mul,
      QuadraticMap.polar_zero_right, add_zero]
  rw [hQA, hpolar, add_zero, hQv]

private lemma cpOp_hblock (n : ℕ) (F : Type) [Field F]
    (hn : 3 ≤ n) (S : Set (GL (Fin n ⊕ Fin n) F)) :
    ∀ ε ∈ Algebra.adjoin F (Units.val '' S), IsIdempotentElem ε →
      formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) ε = ε →
      ∀ x ∈ (Subgroup.centralizer S).comap (Spin.spinMatrix (Spin.quadPlus n F)),
      ∀ y ∈ (Subgroup.centralizer S).comap (Spin.spinMatrix (Spin.quadPlus n F)),
        ∃ w : ↥(spinGroup (Spin.quadPlus n F)),
          ((Spin.spinMatrix (Spin.quadPlus n F)) w :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            ((((Spin.spinMatrix (Spin.quadPlus n F)) x :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) *
             (((Spin.spinMatrix (Spin.quadPlus n F)) y :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε))) =
          ((((Spin.spinMatrix (Spin.quadPlus n F)) y :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) *
            (((Spin.spinMatrix (Spin.quadPlus n F)) x :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε))) := by
  intro ε hεA hεid hεadj x hx y hy
  let Q := Spin.quadPlus n F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hG : IsUnit G.det := cpOp_isUnit_det Q (Spin.nondegenerate_polarBilin_quadPlus n F)
  have hxcomm : ∀ s ∈ (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)),
      Commute ((Spin.spinMatrix Q x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hmem : Spin.spinMatrix Q x ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hx
    exact (congrArg Units.val (Subgroup.mem_centralizer_iff.mp hmem t ht)).symm
  have hxε : ((Spin.spinMatrix Q x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * ((Spin.spinMatrix Q x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hεA hxcomm).eq
  have hycomm : ∀ s ∈ (Units.val '' S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)),
      Commute ((Spin.spinMatrix Q y : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hmem : Spin.spinMatrix Q y ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hy
    exact (congrArg Units.val (Subgroup.mem_centralizer_iff.mp hmem t ht)).symm
  have hyε : ((Spin.spinMatrix Q y : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * ((Spin.spinMatrix Q y : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hεA hycomm).eq
  have hAiso : ∀ v : Fin n ⊕ Fin n → F,
      Q (((Spin.spinMatrix Q x : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec v) = Q v := by
    intro v
    have hmem : (Spin.spinMatrix Q x : GL (Fin n ⊕ Fin n) F) ∈
        (Spin.spinMatrix Q).range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
    exact cpOp_isometry_of_mem_closure Q (Spin.range_spinMatrix_le Q hmem) v
  let X := cpOp_blk (Spin.spinMatrix Q x) ε hεid hxε
  let Y := cpOp_blk (Spin.spinMatrix Q y) ε hεid hyε
  have hXiso : X ∈ cpOp_isoGroup Q := by
    intro v
    change Q (((X : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec v) = Q v
    rw [show (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        ((Spin.spinMatrix Q x : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε) from rfl]
    exact cpOp_blk_isometry Q hG hεid hεadj hxε hAiso v
  have hYiso : Y ∈ cpOp_isoGroup Q := by
    intro v
    change Q (((Y : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec v) = Q v
    rw [show (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        ((Spin.spinMatrix Q y : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε) from rfl]
    exact cpOp_blk_isometry Q hG hεid hεadj hyε
      (by
        intro v
        have hmem : (Spin.spinMatrix Q y : GL (Fin n ⊕ Fin n) F) ∈
            (Spin.spinMatrix Q).range := MonoidHom.mem_range.mpr ⟨y, rfl⟩
        exact cpOp_isometry_of_mem_closure Q (Spin.range_spinMatrix_le Q hmem) v) v
  have hXcl : X ∈ Subgroup.closure {A : GL (Fin n ⊕ Fin n) F |
      ∀ v, Q ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec v) = Q v} :=
    Subgroup.subset_closure hXiso
  have hYcl : Y ∈ Subgroup.closure {A : GL (Fin n ⊕ Fin n) F |
      ∀ v, Q ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec v) = Q v} :=
    Subgroup.subset_closure hYiso
  have hcomm : Y * X * Y⁻¹ * X⁻¹ ∈ CFSG.Open.StatedOmega ⇑Q := by
    have h := Subgroup.commutator_mem_commutator hYcl hXcl
    simpa [CFSG.Open.StatedOmega, commutatorElement_def] using h
  have hrange : (Spin.spinMatrix Q).range = CFSG.Open.StatedOmega ⇑Q := by
    change (Spin.spinMatrix (Spin.quadPlus n F)).range =
      CFSG.Open.StatedOmega ⇑(Spin.quadPlus n F)
    rw [Spin.range_spinMatrix_quadPlus (K := F) hn, Spin.coe_quadPlus]
  have hmem : Y * X * Y⁻¹ * X⁻¹ ∈ (Spin.spinMatrix Q).range := by
    rw [hrange]
    exact hcomm
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨w, ?_⟩
  have hGL : (Spin.spinMatrix Q w) * (X * Y) = Y * X := by
    rw [hw]
    group
  change ((Spin.spinMatrix Q w : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
    ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  simpa only [Units.val_mul] using congrArg Units.val hGL

theorem exists_isComponentOf_glBlockCentralizer_POmegaPlus (n : ℕ) (F : Type) [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (S : Set (GL (Fin n ⊕ Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    (hJ : IsComponentOf J' ((Subgroup.centralizer S).comap (Spin.spinMatrix (Spin.quadPlus n F)))) :
    ∃ ε, IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε ∧
      IsComponentOf J'
        ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε, glBlockCentralizer
        (Spin.spinMatrix (Spin.quadPlus n F)) S ε⁆ := by
  let Q := Spin.quadPlus n F
  let G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hG : IsUnit G.det := cpOp_isUnit_det Q (Spin.nondegenerate_polarBilin_quadPlus n F)
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hj : Function.Injective (Spin.spinMatrix Q) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    change (Spin.spinMatrix (Spin.quadPlus n F)).ker = ⊥
    exact Spin.ker_spinMatrix_quadPlus_eq_bot h2
  obtain ⟨ε, hε, hcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
      (Spin.spinMatrix Q) hj S hS (formAdj (RingHom.id F) G)
      (Geo.formAdj_one (RingHom.id F) hG)
      (fun a _ b _ => Geo.formAdj_add (RingHom.id F) G a b)
      (cpOp_hblock n F hn S) hJ
  refine ⟨ε, ?_, hcomp⟩
  exact (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id F) G
    (Algebra.adjoin F (Units.val '' S)) ε).mp hε

end CFSG.StandardType.ClassicalPosition
