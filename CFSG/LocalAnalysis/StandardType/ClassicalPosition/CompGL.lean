module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompCore

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]

private lemma cpG_mul_block (U V : Matrix ι ι F) (hUV : U * V = 1) (ε : Matrix ι ι F)
    (hε : ε * ε = ε) (hV : V * ε = ε * V) :
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
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hε, sub_self, Matrix.mul_zero]
  have hBC : (1 - ε) * (V * ε) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, ← hV, Matrix.sub_mul,
      Matrix.mul_assoc, hε, sub_self]
  have hBB : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hε, sub_self, sub_zero]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAC, hAB, hBC, hBB, add_zero, zero_add,
    add_sub_cancel]

private lemma cpG_inv_commute (T : GL ι F) (ε : Matrix ι ι F)
    (hT : (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F)) :
    ((T⁻¹ : GL ι F) : Matrix ι ι F) * ε = ε * ((T⁻¹ : GL ι F) : Matrix ι ι F) := by
  have hTT : (T : Matrix ι ι F) * ((T⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hT'T : ((T⁻¹ : GL ι F) : Matrix ι ι F) * (T : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((T⁻¹ : GL ι F) : Matrix ι ι F) * ε
      = ((T⁻¹ : GL ι F) : Matrix ι ι F) * ε * ((T : Matrix ι ι F) *
          ((T⁻¹ : GL ι F) : Matrix ι ι F)) := by rw [hTT, Matrix.mul_one]
    _ = ((T⁻¹ : GL ι F) : Matrix ι ι F) * (ε * (T : Matrix ι ι F)) *
          ((T⁻¹ : GL ι F) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
    _ = ((T⁻¹ : GL ι F) : Matrix ι ι F) * ((T : Matrix ι ι F) * ε) *
          ((T⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hT]
    _ = (((T⁻¹ : GL ι F) : Matrix ι ι F) * (T : Matrix ι ι F)) * ε *
          ((T⁻¹ : GL ι F) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
    _ = ε * ((T⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hT'T, Matrix.one_mul]

private noncomputable def cpG_blk (T : GL ι F) (ε : Matrix ι ι F) (hε : ε * ε = ε)
    (hT : (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F)) : GL ι F :=
  Units.mk ((T : Matrix ι ι F) * ε + (1 - ε)) (((T⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε))
    (cpG_mul_block _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) ε hε
      (cpG_inv_commute T ε hT))
    (cpG_mul_block _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) ε hε hT)

private lemma cpG_commute_adjoin {S : Set (GL ι F)} {T : GL ι F}
    (hT : T ∈ Subgroup.centralizer S) {ε : Matrix ι ι F}
    (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
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
  exact (Subalgebra.mem_centralizer_iff F).mp (Algebra.adjoin_le hgen hε) (T : Matrix ι ι F)
    (Set.mem_singleton (T : Matrix ι ι F))

theorem exists_isComponentOf_glBlockCentralizer_GL [Finite F] (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {J' : Subgroup (GL ι F)}
    (hJ : IsComponentOf J' (Subgroup.centralizer S)) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e ∧
      IsComponentOf J' ⁅glBlockCentralizer (MonoidHom.id (GL ι F)) S e,
        glBlockCentralizer (MonoidHom.id (GL ι F)) S e⁆ := by
  obtain ⟨e, heprim, hcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer (U := GL ι F) (ι := ι)
      (F := F) (MonoidHom.id (GL ι F)) Function.injective_id S hS id rfl (fun a _ b _ => rfl)
      (fun ε hε hid _ x hx y hy => by
        have hxc : (x : Matrix ι ι F) * ε = ε * (x : Matrix ι ι F) :=
          cpG_commute_adjoin (Subgroup.mem_comap.mp hx) hε
        have hyc : (y : Matrix ι ι F) * ε = ε * (y : Matrix ι ι F) :=
          cpG_commute_adjoin (Subgroup.mem_comap.mp hy) hε
        let X : GL ι F := cpG_blk x ε hid hxc
        let Y : GL ι F := cpG_blk y ε hid hyc
        refine ⟨Y * X * (X * Y)⁻¹, ?_⟩
        have h : Y * X * (X * Y)⁻¹ * (X * Y) = Y * X := by group
        exact congrArg Units.val h)
      (by rwa [Subgroup.comap_id])
  exact ⟨e, (Block.isPrimStarIdemIn_id_iff _ _).mp heprim, hcomp⟩

end CFSG.StandardType.ClassicalPosition
