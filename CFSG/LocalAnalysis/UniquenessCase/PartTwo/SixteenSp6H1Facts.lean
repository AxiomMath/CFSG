module

public import CFSG.Quasithin.Background.JonesParshallSymplecticBinary
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
  CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def s16spQ0 (x : Fin 3 ⊕ Fin 3 → ZMod 2) : ZMod 2 :=
  ∑ i : Fin 3, x (Sum.inl i) * x (Sum.inr i)

theorem s16spQ0_add (x y : Fin 3 ⊕ Fin 3 → ZMod 2) :
    s16spQ0 (x + y) = s16spQ0 x + s16spQ0 y + spForm 3 (ZMod 2) x y := by
  simp only [s16spQ0, Pi.add_apply, spForm_apply, dotProduct, Fintype.sum_sum_type,
    spJ_mulVec_inl, spJ_mulVec_inr, CharTwo.neg_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem s16sp_no_invariant (l : Module.Dual (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2)) :
    ¬ ∀ (g : bilinIsometryGroup (spForm 3 (ZMod 2))) (x : Fin 3 ⊕ Fin 3 → ZMod 2),
      s16spQ0 (sE g x) + l (sE g x) = s16spQ0 x + l x := by
  intro h
  refine not_invariant_of_polar_eq (b := spForm 3 (ZMod 2)) spForm_isAlt spForm_nondegenerate
    (by simp [Nat.card_eq_fintype_card]) (fun x => s16spQ0 x + l x) ?_ ?_
  · intro x y
    simp only [s16spQ0_add, map_add]
    ring
  · intro s x
    exact h s x

theorem s16sp_finrank_H1_le_one :
    Module.finrank (ZMod 2)
      (H1 (Representation.dual (binarySymplecticNatural (spForm 3 (ZMod 2))))) ≤ 1 :=
  finrank_H1_binarySymplecticNatural_dual_le_one spForm_isAlt spForm_nondegenerate

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
