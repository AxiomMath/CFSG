module

public import CFSG.Monster.Griess.Short
import CFSG.Monster.Code.LatticeGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess Subgroup

theorem toAdd_projQ (r : Q) : Multiplicative.toAdd (projQ r) = coordOf r := rfl

theorem setOf_isShort_eq : {r : Q | IsShort (QuotientGroup.mk r)} =
    {r : Q | IsShortCoord (coordOf r)} :=
  Set.ext fun r => isShort_mk_iff r

instance instFiniteQ : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; positivity)

private theorem cls_eq_classOf {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    cls u hu = classOf u := by
  unfold classOf
  exact (dite_eq_left hu).symm

theorem map_closure_short_projQ :
    (closure {r : Q | IsShortCoord (coordOf r)}).map projQ = ⊤ := by
  set H := closure {r : Q | IsShortCoord (coordOf r)}
  have hmemL : ∀ {w : Fin 24 → ℤ}, w ∈ AddSubgroup.closure latticeGens → w ∈ codeLattice C :=
    fun {w} hw => by
      rw [closure_latticeGens] at hw
      exact hw
  have key : ∀ (w : Fin 24 → ℤ) (hw : w ∈ AddSubgroup.closure latticeGens),
      Multiplicative.ofAdd (phi0Equiv.symm (cls w (hmemL hw))) ∈ H.map projQ := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem u hu =>
      have hmin : u ∈ minVecs := mem_minVecs_iff.2 (latticeGens_mem hu)
      set x := phi0Equiv.symm (cls u (hmemL (AddSubgroup.subset_closure hu)))
      have hx : IsShortCoord x := ⟨u, hmin, by
        rw [← cls_eq_classOf hmin.1]
        exact (phi0Equiv.apply_symm_apply _).symm⟩
      refine ⟨rep x, subset_closure ?_, ?_⟩
      · change IsShortCoord (coordOf (rep x))
        rw [coordOf_rep]
        exact hx
      · change Multiplicative.ofAdd (coordOf (rep x)) = Multiplicative.ofAdd x
        rw [coordOf_rep]
    | zero =>
      have h0 : cls (0 : Fin 24 → ℤ) (hmemL (AddSubgroup.zero_mem _)) = 0 := rfl
      rw [h0, map_zero, ofAdd_zero]
      exact one_mem _
    | add w w' hw hw' ihw ihw' =>
      have h : cls (w + w') (hmemL (AddSubgroup.add_mem _ hw hw')) =
          cls w (hmemL hw) + cls w' (hmemL hw') := (cls_add _ _).symm
      rw [h, map_add, ofAdd_add]
      exact mul_mem ihw ihw'
    | neg w hw ihw =>
      have h : cls (-w) (hmemL (AddSubgroup.neg_mem _ hw)) = -cls w (hmemL hw) := rfl
      rw [h, map_neg, ofAdd_neg]
      exact inv_mem ihw
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (phi0Equiv (Multiplicative.toAdd y))
  have hw' : (w : Fin 24 → ℤ) ∈ AddSubgroup.closure latticeGens := by
    rw [closure_latticeGens]
    exact w.2
  have h := key w hw'
  have e : cls (w : Fin 24 → ℤ) (hmemL hw') = phi0Equiv (Multiplicative.toAdd y) := hw
  rw [e, LinearEquiv.symm_apply_apply, ofAdd_toAdd] at h
  exact h

theorem closure_isShortCoord_eq_top : closure {r : Q | IsShortCoord (coordOf r)} = ⊤ := by
  refine frattini_nongenerating ?_
  have h := comap_map_eq projQ (closure {r : Q | IsShortCoord (coordOf r)})
  rw [map_closure_short_projQ, comap_top, ker_projQ, center_Q, ← frattini_Q] at h
  exact h.symm

theorem closure_isShort_eq_top : closure {r : Q | IsShort (QuotientGroup.mk r)} = ⊤ := by
  rw [setOf_isShort_eq]
  exact closure_isShortCoord_eq_top

theorem closure_coe_isShort_eq_Q :
    closure ((↑) '' {r : Q | IsShort (QuotientGroup.mk r)} : Set (GL SpinIdx ℚ)) = Q := by
  have h := MonoidHom.map_closure Q.subtype {r : Q | IsShort (QuotientGroup.mk r)}
  rw [closure_isShort_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h.symm

end CFSG.Monster.Visible
