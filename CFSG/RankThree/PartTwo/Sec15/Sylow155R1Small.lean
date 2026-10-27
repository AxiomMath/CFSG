module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
public import CFSG.Open.PGLModelDefs
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1SmallLem

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1AutCent_of_forall_eq_one {Y : Type} [Group Y]
    (h : ∀ (α : MulAut Y) (y : Y), orderOf y = 3 → Nat.Coprime (orderOf α) 6 → α y = y →
      α = 1) : Res1AutCent Y := by
  intro α V y hy hα hαy _ _ _ v _
  rw [h α y hy hα hαy, one_mul, mul_one]

private theorem projSL_eq_range (n : ℕ) (K : Type) [Field K] :
    CFSG.PGLModel.projSL n K = (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).range := by
  rw [CFSG.PGLModel.projSL, CFSG.PGLModel.projImage, Matrix.SpecialLinearGroup.toPGL,
    MonoidHom.range_comp, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

private theorem nonempty_sl_equiv_projSL {n : ℕ} {K : Type} [Field K]
    (h : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥) :
    Nonempty (Matrix.SpecialLinearGroup (Fin n) K ≃* ↥(CFSG.PGLModel.projSL n K)) := by
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K) := by
    rw [← MonoidHom.ker_eq_bot_iff, Matrix.SpecialLinearGroup.toPGL_ker, h]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (projSL_eq_range n K).symm)⟩

private theorem nonempty_sl_equiv_of_ringEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (n : ℕ) : Nonempty (Matrix.SpecialLinearGroup (Fin n) K ≃*
      Matrix.SpecialLinearGroup (Fin n) L) :=
  ⟨{ toFun := Matrix.SpecialLinearGroup.map e.toRingHom
     invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
     left_inv := fun g => by ext i j; simp
     right_inv := fun g => by ext i j; simp
     map_mul' := map_mul _ }⟩

private theorem nonempty_projSL_two_four_equiv_alt5 :
    Nonempty (↥(CFSG.PGLModel.projSL 2 (GaloisField 2 2)) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := nonempty_sl_equiv_projSL (n := 2) (K := GaloisField 2 2)
    (CFSG.CGT.PushingUpLit.CGT6.sl2_center_eq_bot _)
  obtain ⟨e₂⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
  exact ⟨e₁.symm.trans e₂⟩

private theorem nonempty_projSL_three_two_equiv_sl3 :
    Nonempty (↥(CFSG.PGLModel.projSL 3 (GaloisField 2 1)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let e : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP (p := 2)).toRingEquiv
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      apply e.injective
      have h3 : (e r) ^ 3 = 1 := by rw [← map_pow, hr, map_one]
      rw [map_one]
      revert h3
      generalize e r = t
      revert t
      decide +kernel
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrg, hr1, map_one]
    rfl
  obtain ⟨e₁⟩ := nonempty_sl_equiv_projSL hcenter
  obtain ⟨e₂⟩ := nonempty_sl_equiv_of_ringEquiv e 3
  exact ⟨e₁.symm.trans e₂⟩

theorem res1AutCent_projSL_two_four :
    Res1AutCent ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 2)) := by
  obtain ⟨e⟩ := nonempty_projSL_two_four_equiv_alt5
  exact Res1AutCent.of_mulEquiv e
    (res1AutCent_of_forall_eq_one fun α y hy hα hαy => alt5_aut_eq_one α y hy hα hαy)

theorem res1AutCent_projSL_three_two :
    Res1AutCent ↥(CFSG.PGLModel.projSL 3 (GaloisField 2 1)) := by
  obtain ⟨e⟩ := nonempty_projSL_three_two_equiv_sl3
  exact Res1AutCent.of_mulEquiv e
    (res1AutCent_of_forall_eq_one fun α y hy hα hαy => sl3_two_aut_eq_one α y hy hα hαy)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
