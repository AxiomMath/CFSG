module

public import CFSG.Monster.Griess.ModFive.Lattice
import CFSG.Monster.Visible.ShortGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.ModFive

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

theorem exists_scalar_of_commute_Rmat_mod5 {s : Matrix SpinIdx SpinIdx ℚ} (hs : IsR5 s)
    (hc : ∀ c : ShortIdx, IsD5 (s * Rmat c - Rmat c * s)) :
    ∃ t ∈ R5, IsD5 (s - t • (1 : Matrix SpinIdx SpinIdx ℚ)) := by
  classical
  let sr : Matrix SpinIdx SpinIdx R5 := Matrix.of fun a b => ⟨s a b, hs a b⟩
  have hsr : R5.subtype.mapMatrix sr = s := by
    ext a b
    rfl
  let s5 : Matrix SpinIdx SpinIdx (ZMod 5) := (ratLocalRed 5).mapMatrix sr
  have hR : ∀ c : ShortIdx, R5.subtype.mapMatrix (qmatR R5 0 c.1.1 c.1.2) = Rmat c := fun c => by
    rw [RingHom.mapMatrix_apply, map_qmatR]
    rfl
  have hcomm : ∀ c : ShortIdx,
      Commute (qmatR (ZMod 5) 0 c.1.1 c.1.2) s5 := by
    intro c
    have h0 : (ratLocalRed 5).mapMatrix (sr * qmatR R5 0 c.1.1 c.1.2 - qmatR R5 0 c.1.1 c.1.2 * sr) =
        0 := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
        ratLocalRed_eq_zero_iff_mem_D5]
      have := hc c a b
      rw [← hsr, ← hR, ← map_mul, ← map_mul, ← map_sub] at this
      exact this
    rw [map_sub, map_mul, map_mul, RingHom.mapMatrix_apply (ratLocalRed 5) (qmatR R5 0 _ _),
      map_qmatR, sub_eq_zero] at h0
    exact h0.symm
  let H : Subgroup Q :=
    { carrier := {r | Commute ((reduceQ (ZMod 5) r : GL SpinIdx (ZMod 5)) :
        Matrix SpinIdx SpinIdx (ZMod 5)) s5}
      mul_mem' := fun {a b} ha hb => by
        change Commute ((reduceQ (ZMod 5) (a * b) : GL SpinIdx (ZMod 5)) :
          Matrix SpinIdx SpinIdx (ZMod 5)) s5
        rw [map_mul, Units.val_mul]
        exact ha.mul_left hb
      one_mem' := by
        change Commute ((reduceQ (ZMod 5) 1 : GL SpinIdx (ZMod 5)) :
          Matrix SpinIdx SpinIdx (ZMod 5)) s5
        rw [map_one, Units.val_one]
        exact Commute.one_left _
      inv_mem' := fun {a} ha => by
        change Commute ((reduceQ (ZMod 5) a⁻¹ : GL SpinIdx (ZMod 5)) :
          Matrix SpinIdx SpinIdx (ZMod 5)) s5
        rw [map_inv]
        exact ha.units_inv_left }
  have hshort : ∀ r : Q, IsShortCoord (coordOf r) → r ∈ H := by
    intro r hr
    change Commute ((reduceQ (ZMod 5) r : GL SpinIdx (ZMod 5)) :
      Matrix SpinIdx SpinIdx (ZMod 5)) s5
    have e : ((reduceQ (ZMod 5) r : GL SpinIdx (ZMod 5)) : Matrix SpinIdx SpinIdx (ZMod 5)) =
        sgnR (ZMod 5) (centralCoord r) • qmatR (ZMod 5) 0 (coordOf r).1 (coordOf r).2 := by
      conv_lhs => rw [← spinEquiv.apply_symm_apply r]
      rw [coe_reduceQ_spinEquiv, sgnR_smul_qmatR, add_zero]
      rfl
    rw [e]
    exact (hcomm ⟨coordOf r, hr⟩).smul_left _
  have htop : (⊤ : Subgroup Q) ≤ H := by
    rw [← Visible.closure_isShortCoord_eq_top, Subgroup.closure_le]
    exact fun r hr => hshort r hr
  have hTD : ∀ p : C × Cocode, TDR (ZMod 5) p * s5 = s5 * TDR (ZMod 5) p := by
    intro p
    have h := htop (Subgroup.mem_top (spinEquiv ⟨0, p.1, p.2⟩))
    change Commute ((reduceQ (ZMod 5) (spinEquiv ⟨0, p.1, p.2⟩) : GL SpinIdx (ZMod 5)) :
      Matrix SpinIdx SpinIdx (ZMod 5)) s5 at h
    rw [coe_reduceQ_spinEquiv] at h
    rw [TDR_eq_qmatR]
    exact h.eq
  obtain ⟨t5, ht5⟩ := mem_range_scalar_of_forall_commute_TDR (by decide : (2 : ZMod 5) ≠ 0) hTD
  have hs5 : ∀ a b, ratLocalRed 5 (sr a b) = if a = b then t5 else 0 := fun a b => by
    have h := congrFun (congrFun ht5 a) b
    rw [Matrix.scalar_apply, Matrix.diagonal_apply] at h
    exact h.symm
  have htR : ratLocalRed 5 (t5.val : R5) = t5 := by rw [map_natCast, ZMod.natCast_zmod_val]
  refine ⟨((t5.val : R5) : ℚ), (t5.val : R5).2, fun a b => ?_⟩
  rcases eq_or_ne a b with rfl | hab
  · have e : (s - ((t5.val : R5) : ℚ) • (1 : Matrix SpinIdx SpinIdx ℚ)) a a =
        ((sr a a - (t5.val : R5) : R5) : ℚ) := by
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rfl
    rw [e, ← ratLocalRed_eq_zero_iff_mem_D5, map_sub, hs5, ite_eq_left rfl, htR, sub_self]
  · have e : (s - ((t5.val : R5) : ℚ) • (1 : Matrix SpinIdx SpinIdx ℚ)) a b =
        ((sr a b : R5) : ℚ) := by
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hab, smul_zero, sub_zero]
      rfl
    rw [e, ← ratLocalRed_eq_zero_iff_mem_D5, hs5, ite_eq_right hab]

end CFSG.Monster.Griess.ModFive
