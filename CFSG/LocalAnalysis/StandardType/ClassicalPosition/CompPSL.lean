module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompCore

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly

private lemma cpL_mul_block {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (U V : Matrix ι ι F) (hUV : U * V = 1)
    (ε : Matrix ι ι F) (hε : ε * ε = ε)
    (hV : V * ε = ε * V) :
    (U * ε + (1 - ε)) * (V * ε + (1 - ε)) = 1 := by
  have hAC : (U * ε) * (V * ε) = ε := by
    calc (U * ε) * (V * ε)
        = U * (ε * (V * ε)) := by rw [Matrix.mul_assoc]
      _ = U * ((ε * V) * ε) := by rw [Matrix.mul_assoc]
      _ = U * ((V * ε) * ε) := by rw [← hV]
      _ = U * (V * (ε * ε)) := by rw [Matrix.mul_assoc]
      _ = U * (V * ε) := by rw [hε]
      _ = (U * V) * ε := by rw [Matrix.mul_assoc]
      _ = ε := by rw [hUV, Matrix.one_mul]
  have hAB : (U * ε) * (1 - ε) = 0 := by
    calc (U * ε) * (1 - ε)
        = U * (ε * (1 - ε)) := by rw [Matrix.mul_assoc]
      _ = U * (ε * 1 - ε * ε) := by rw [Matrix.mul_sub]
      _ = U * (ε - ε) := by rw [Matrix.mul_one, hε]
      _ = U * 0 := by rw [sub_self]
      _ = 0 := Matrix.mul_zero U
  have hBC : (1 - ε) * (V * ε) = 0 := by
    calc (1 - ε) * (V * ε)
        = ((1 - ε) * V) * ε := by rw [Matrix.mul_assoc]
      _ = (1 * V - ε * V) * ε := by rw [Matrix.sub_mul]
      _ = (V - V * ε) * ε := by rw [Matrix.one_mul, ← hV]
      _ = V * ε - (V * ε) * ε := by rw [Matrix.sub_mul]
      _ = V * ε - V * (ε * ε) := by rw [Matrix.mul_assoc]
      _ = V * ε - V * ε := by rw [hε]
      _ = 0 := sub_self _
  have hBB : (1 - ε) * (1 - ε) = 1 - ε := by
    calc (1 - ε) * (1 - ε)
        = (1 - ε) * 1 - (1 - ε) * ε := by rw [Matrix.mul_sub]
      _ = (1 - ε) - (1 * ε - ε * ε) := by rw [Matrix.mul_one, Matrix.sub_mul]
      _ = (1 - ε) - (ε - ε) := by rw [Matrix.one_mul, hε]
      _ = 1 - ε := by rw [sub_self, sub_zero]
  calc (U * ε + (1 - ε)) * (V * ε + (1 - ε))
      = (U * ε) * (V * ε) + (U * ε) * (1 - ε) +
          ((1 - ε) * (V * ε) + (1 - ε) * (1 - ε)) := by
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    _ = ε + 0 + (0 + (1 - ε)) := by rw [hAC, hAB, hBC, hBB]
    _ = 1 := by abel

private lemma cpL_inv_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (T : GL ι F) (ε : Matrix ι ι F)
    (hT : (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F)) :
    (((T⁻¹ : GL ι F)) : Matrix ι ι F) * ε =
      ε * (((T⁻¹ : GL ι F)) : Matrix ι ι F) := by
  have hTT : (T : Matrix ι ι F) * (((T⁻¹ : GL ι F)) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hT'T : (((T⁻¹ : GL ι F)) : Matrix ι ι F) * (T : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hL : (((T⁻¹ : GL ι F)) : Matrix ι ι F) * ((T : Matrix ι ι F) * ε) *
      (((T⁻¹ : GL ι F)) : Matrix ι ι F) =
      ε * (((T⁻¹ : GL ι F)) : Matrix ι ι F) := by
    calc (((T⁻¹ : GL ι F)) : Matrix ι ι F) * ((T : Matrix ι ι F) * ε) *
          (((T⁻¹ : GL ι F)) : Matrix ι ι F)
        = (((((T⁻¹ : GL ι F)) : Matrix ι ι F) * (T : Matrix ι ι F)) * ε) *
            (((T⁻¹ : GL ι F)) : Matrix ι ι F) := by rw [← Matrix.mul_assoc]
      _ = (1 : Matrix ι ι F) * ε * (((T⁻¹ : GL ι F)) : Matrix ι ι F) := by
            rw [hT'T]
      _ = ε * (((T⁻¹ : GL ι F)) : Matrix ι ι F) := by rw [Matrix.one_mul]
  have hR : (((T⁻¹ : GL ι F)) : Matrix ι ι F) * (ε * (T : Matrix ι ι F)) *
      (((T⁻¹ : GL ι F)) : Matrix ι ι F) =
      (((T⁻¹ : GL ι F)) : Matrix ι ι F) * ε := by
    calc (((T⁻¹ : GL ι F)) : Matrix ι ι F) * (ε * (T : Matrix ι ι F)) *
          (((T⁻¹ : GL ι F)) : Matrix ι ι F)
        = ((((T⁻¹ : GL ι F)) : Matrix ι ι F) * ε) *
            ((T : Matrix ι ι F) * (((T⁻¹ : GL ι F)) : Matrix ι ι F)) := by
            rw [← Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ((((T⁻¹ : GL ι F)) : Matrix ι ι F) * ε) * 1 := by rw [hTT]
      _ = (((T⁻¹ : GL ι F)) : Matrix ι ι F) * ε := by rw [Matrix.mul_one]
  have h := congrArg (fun A : Matrix ι ι F =>
    (((T⁻¹ : GL ι F)) : Matrix ι ι F) * A * (((T⁻¹ : GL ι F)) : Matrix ι ι F)) hT
  rw [hL, hR] at h
  exact h.symm

private noncomputable def cpL_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (T : GL ι F) (ε : Matrix ι ι F) (hε : ε * ε = ε)
    (hT : (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F)) : GL ι F :=
  Units.mk ((T : Matrix ι ι F) * ε + (1 - ε))
    ((((T⁻¹ : GL ι F)) : Matrix ι ι F) * ε + (1 - ε))
    (cpL_mul_block (T : Matrix ι ι F) (((T⁻¹ : GL ι F)) : Matrix ι ι F)
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      ε hε (cpL_inv_commute T ε hT))
    (cpL_mul_block (((T⁻¹ : GL ι F)) : Matrix ι ι F) (T : Matrix ι ι F)
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
      ε hε hT)

private lemma cpL_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {T : GL ι F} (hT : T ∈ Subgroup.centralizer S)
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F) := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :
        Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA hε) (T : Matrix ι ι F)
    (Set.mem_singleton (T : Matrix ι ι F))

private lemma cpL_det_comm {G : Type} [CommGroup G] (a b : G) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  calc a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) := by group
    _ = (a * b) * (b * a)⁻¹ := by rw [mul_inv_rev]
    _ = (a * b) * (a * b)⁻¹ := by rw [mul_comm b a]
    _ = 1 := mul_inv_cancel _

private lemma cpL_hblock (m : ℕ) (F : Type) [Field F]
    (S : Set (GL (Fin (m + 1)) F))
    (ε : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) (hid : IsIdempotentElem ε)
    (x y : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (hx : x ∈ (Subgroup.centralizer S).comap Matrix.SpecialLinearGroup.toGL)
    (hy : y ∈ (Subgroup.centralizer S).comap Matrix.SpecialLinearGroup.toGL) :
    ∃ w : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      (Matrix.SpecialLinearGroup.toGL w : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (((Matrix.SpecialLinearGroup.toGL x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ε +
            (1 - ε)) *
          ((Matrix.SpecialLinearGroup.toGL y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ε +
            (1 - ε))) =
        ((Matrix.SpecialLinearGroup.toGL y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ε +
            (1 - ε)) *
          ((Matrix.SpecialLinearGroup.toGL x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ε +
            (1 - ε)) := by
  have hx' : Matrix.SpecialLinearGroup.toGL x ∈ Subgroup.centralizer S :=
    Subgroup.mem_comap.mp hx
  have hy' : Matrix.SpecialLinearGroup.toGL y ∈ Subgroup.centralizer S :=
    Subgroup.mem_comap.mp hy
  have hxcomm : (Matrix.SpecialLinearGroup.toGL x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ε = ε * (Matrix.SpecialLinearGroup.toGL x :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    cpL_commute_adjoin hx' hε
  have hycomm : (Matrix.SpecialLinearGroup.toGL y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ε = ε * (Matrix.SpecialLinearGroup.toGL y :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    cpL_commute_adjoin hy' hε
  let X : GL (Fin (m + 1)) F :=
    cpL_blk (Matrix.SpecialLinearGroup.toGL x) ε hid hxcomm
  let Y : GL (Fin (m + 1)) F :=
    cpL_blk (Matrix.SpecialLinearGroup.toGL y) ε hid hycomm
  have hXval : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (Matrix.SpecialLinearGroup.toGL x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ε +
        (1 - ε) := rfl
  have hYval : (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (Matrix.SpecialLinearGroup.toGL y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * ε +
        (1 - ε) := rfl
  let c : GL (Fin (m + 1)) F := Y * X * Y⁻¹ * X⁻¹
  have hdet : Matrix.GeneralLinearGroup.det c = 1 := by
    dsimp only [c]
    simpa only [map_mul, map_inv] using
      cpL_det_comm (Matrix.GeneralLinearGroup.det Y) (Matrix.GeneralLinearGroup.det X)
  have hdetMat : (c : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply c, hdet, Units.val_one]
  let w : Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
    ⟨(c : Matrix (Fin (m + 1)) (Fin (m + 1)) F), hdetMat⟩
  refine ⟨w, ?_⟩
  have hw : Matrix.SpecialLinearGroup.toGL w = c := by
    apply Units.ext
    rfl
  have hgroup : c * (X * Y) = Y * X := by
    dsimp only [c]
    group
  have hgroup' : (c : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) =
      (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    have h := congrArg (fun u : GL (Fin (m + 1)) F =>
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hgroup
    simpa [Units.val_mul] using h
  rw [hw]
  simpa only [hXval, hYval] using hgroup'

theorem exists_isComponentOf_glBlockCentralizer_PSL (m : ℕ) (F : Type) [Field F] [Finite F]
    (S : Set (GL (Fin (m + 1)) F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)}
    (hJ : IsComponentOf J' ((Subgroup.centralizer S).comap Matrix.SpecialLinearGroup.toGL)) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e ∧
      IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ := by
  obtain ⟨e, heprim, hcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
      (U := Matrix.SpecialLinearGroup (Fin (m + 1)) F)
      (ι := Fin (m + 1)) (F := F)
      (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (m + 1)) F →*
          GL (Fin (m + 1)) F)
      Matrix.SpecialLinearGroup.toGL_injective
      S hS id rfl (fun a _ b _ => rfl)
      (fun ε hε hid _ x hx y hy => cpL_hblock m F S ε hε hid x y hx hy)
      hJ
  exact ⟨e, (Block.isPrimStarIdemIn_id_iff _ _).mp heprim, hcomp⟩

end CFSG.StandardType.ClassicalPosition
