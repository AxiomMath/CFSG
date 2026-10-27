module

public import CFSG.OddTranspositions.O4CloseReduction
import CFSG.OddTranspositions.O4PairTriple

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity CFSG.GroupTheory
open CFSG.OddTranspositions.QZ

private def o4TriDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

private instance (priority := 2000) o4TriDecEqInst : DecidableEq F25t := o4TriDecEq

private def o4TriP : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨0, 1⟩, ⟨1, 0⟩; ⟨4, 0⟩, ⟨0, 0⟩], by rw [Matrix.det_fin_two_of]; decide +kernel⟩

private def o4TriQ : Matrix.SpecialLinearGroup (Fin 2) F25t :=
  ⟨!![⟨1, 0⟩, ⟨0, 3⟩; ⟨0, 0⟩, ⟨1, 0⟩], by rw [Matrix.det_fin_two_of]; decide +kernel⟩

private abbrev o4TriFrob : Matrix.SpecialLinearGroup (Fin 2) F25t →*
    Matrix.SpecialLinearGroup (Fin 2) F25t :=
  Matrix.SpecialLinearGroup.map frob25t.toRingHom

private theorem o4TriQ_mul_frob_P : o4TriQ * o4TriFrob o4TriP = o4TriP := by
  decide +kernel

private theorem o4TriQ_not_fixed : ¬ (o4TriQ = o4TriFrob o4TriQ ∨ o4TriQ = -o4TriFrob o4TriQ) := by
  decide +kernel

private theorem o4Tri_not_commute_mat :
    ¬ (o4TriQ * o4TriFrob Ma = Ma * o4TriFrob o4TriQ ∨
      o4TriQ * o4TriFrob Ma = -(Ma * o4TriFrob o4TriQ)) := by
  decide +kernel

private theorem o4Tri_sq_ne :
    ¬ (o4TriFrob Ma * o4TriQ * o4TriFrob (o4TriFrob Ma * o4TriQ) *
          (o4TriFrob Ma * o4TriQ * o4TriFrob (o4TriFrob Ma * o4TriQ)) = 1 ∨
        o4TriFrob Ma * o4TriQ * o4TriFrob (o4TriFrob Ma * o4TriQ) *
          (o4TriFrob Ma * o4TriQ * o4TriFrob (o4TriFrob Ma * o4TriQ)) = -1) := by
  decide +kernel

private def o4TriY : PSigmaL2t := SemidirectProduct.mk (CFSG.PSL2Table.mk o4TriQ) frob25t

private theorem o4Tri_psl2FieldAut_mk (σ : F25t ≃+* F25t)
    (A : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    CFSG.GorensteinWalter.psl2FieldAut F25t σ (CFSG.PSL2Table.mk A) =
      CFSG.PSL2Table.mk (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  rw [CFSG.Walter.psl2FieldAut_eq_psl2Map]
  rfl

private theorem o4TriY_mem_class65t : o4TriY ∈ class65t := by
  refine (mem_class65t_iff_left_right o4TriY).mpr ⟨?_, rfl⟩
  refine mem_St_iff.mpr ⟨o4TriP, ?_⟩
  change CFSG.PSL2Table.mk o4TriQ = _
  rw [eq_mul_inv_iff_mul_eq, ← map_mul]
  exact congrArg _ o4TriQ_mul_frob_P

private theorem not_commute_wT_o4TriY : ¬ Commute wT o4TriY := by
  intro h
  have hl := congrArg SemidirectProduct.left h.eq
  change 1 * CFSG.GorensteinWalter.psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk o4TriQ) =
    CFSG.PSL2Table.mk o4TriQ * CFSG.GorensteinWalter.psl2FieldAut F25t frob25t 1 at hl
  rw [one_mul, map_one, mul_one, o4Tri_psl2FieldAut_mk, CFSG.PSL2Table.mk_eq_mk_iff] at hl
  exact o4TriQ_not_fixed hl

private theorem not_commute_uT_o4TriY : ¬ Commute uT o4TriY := by
  intro h
  have hl := congrArg SemidirectProduct.left h.eq
  change CFSG.PSL2Table.mk Ma *
      CFSG.GorensteinWalter.psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk o4TriQ) =
    CFSG.PSL2Table.mk o4TriQ *
      CFSG.GorensteinWalter.psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk Ma) at hl
  rw [o4Tri_psl2FieldAut_mk, o4Tri_psl2FieldAut_mk, ← map_mul, ← map_mul,
    CFSG.PSL2Table.mk_eq_mk_iff] at hl
  exact o4Tri_not_commute_mat hl

private theorem wT_mul_uT_mul_o4TriY :
    wT * uT * o4TriY =
      SemidirectProduct.mk (CFSG.PSL2Table.mk (o4TriFrob Ma * o4TriQ)) frob25t := by
  apply SemidirectProduct.ext
  · change 1 * CFSG.GorensteinWalter.psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk Ma) *
        CFSG.GorensteinWalter.psl2FieldAut F25t (frob25t * frob25t)
          (CFSG.PSL2Table.mk o4TriQ) = _
    rw [frob25t_mul_self, map_one, MulAut.one_apply, one_mul, o4Tri_psl2FieldAut_mk, ← map_mul]
  · change frob25t * frob25t * frob25t = frob25t
    rw [frob25t_mul_self, one_mul]

private theorem o4Tri_mk_frob_sq (a : CFSG.GorensteinWalter.PSL2 F25t) :
    (SemidirectProduct.mk a frob25t : PSigmaL2t) ^ 2 =
      SemidirectProduct.inl (a * CFSG.GorensteinWalter.psl2FieldAut F25t frob25t a) := by
  rw [pow_two]
  apply SemidirectProduct.ext
  · rfl
  · exact frob25t_mul_self

private theorem orderOf_wT_mul_uT_mul_o4TriY_ne_four : orderOf (wT * uT * o4TriY) ≠ 4 := by
  intro h4
  have h1 := pow_orderOf_eq_one (wT * uT * o4TriY)
  rw [h4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, wT_mul_uT_mul_o4TriY, o4Tri_mk_frob_sq,
    ← map_pow, map_eq_one_iff _ SemidirectProduct.inl_injective, o4Tri_psl2FieldAut_mk,
    ← map_mul, ← map_pow, CFSG.PSL2Table.mk_eq_one_iff, pow_two] at h1
  exact o4Tri_sq_ne h1

theorem exists_triangle_ne_four_of_o4PairData {Y : Type} [Group Y] {Θ : Set Y}
    (hP : O4PairData Y Θ) : ∃ x y t : Y, IsTriangle Θ x y t ∧ orderOf (x * t * y) ≠ 4 := by
  obtain ⟨e, he⟩ := hP
  let f : PSigmaL2t ≃* Y := psigmaL2Equiv.trans e.symm
  have hmem : ∀ a ∈ class65t, f a ∈ Θ := by
    intro a ha
    have h1 : psigmaL2Equiv a ∈ e '' Θ := by
      rw [he, ← psigmaL2Equiv_image_class65t]
      exact Set.mem_image_of_mem _ ha
    obtain ⟨z, hz, hza⟩ := h1
    have hfa : f a = z := by
      change e.symm (psigmaL2Equiv a) = z
      rw [← hza, MulEquiv.symm_apply_apply]
    rw [hfa]
    exact hz
  refine ⟨f wT, f o4TriY, f uT, ⟨hmem _ wT_mem_class65t, hmem _ uT_mem_class65t,
    hmem _ o4TriY_mem_class65t, fun h => uT_ne_wT (f.injective h).symm,
    commute_uT_wT.symm.map f, fun h => not_commute_wT_o4TriY (h.of_map f.injective),
    fun h => not_commute_uT_o4TriY (h.of_map f.injective)⟩, ?_⟩
  rw [← map_mul, ← map_mul, MulEquiv.orderOf_eq]
  exact orderOf_wT_mul_uT_mul_o4TriY_ne_four

end CFSG.OddTranspositions

end
