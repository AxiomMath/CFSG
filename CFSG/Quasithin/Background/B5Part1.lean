module

public import CFSG.Quasithin.Background.B5Irr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section Part1

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem genFitting_eq_of_eq (h : B51Hyp G L) (hGL : G = L) : quasithinGenFitting G = L := by
  have h1 := genFitting_sup_eq h (T := ⊥) bot_le (IsPGroup.of_card (n := 0) (by simp))
  rw [sup_bot_eq] at h1
  rw [hGL]
  exact h1

theorem genFitting_eq_of_eq_sup (h : B51Hyp G L) {T : Subgroup (MulAut V)} (hT : IsSylowTwoOf T G)
    (hGL : G = L ⊔ T) : quasithinGenFitting G = L := by
  rw [hGL]
  exact genFitting_sup_eq h hT.1 hT.2.1

theorem part1_of_irr (hI : B51IrrInputs) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∈ IrrPlus L ⊤) : B51Part1 G L := by
  have h1 := b51_case1i hI hV h hU
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  refine ⟨?_, Or.inl h1⟩
  rcases h1.2.2 T hT with hGL | ⟨hGL, -⟩
  · exact genFitting_eq_of_eq h hGL
  · exact genFitting_eq_of_eq_sup h hT hGL

@[expose] def AsB51P2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ G L : Subgroup (MulAut V),
    B51Hyp G L → B51Part1 G L → ¬ IsIntDirect (commV L) (fixV L) ⊤ →
      commV L ∈ IrrPlus L ⊤ ∧ B51NaturalList2 L (commV L) (fixV L ⊓ commV L)

@[expose] def AsB51P5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ G L : Subgroup (MulAut V),
    B51Hyp G L → B51Part1 G L → B51Part5 G L

omit [Finite V] in
theorem b51_part2_equiv (L : Subgroup (MulAut V)) :
    ¬ IsIntDirect (commV L) (fixV L) ⊤ ↔ (fixV L ⊓ commV L ≠ ⊥ ∨ commV L ⊔ fixV L < ⊤) := by
  unfold IsIntDirect
  rw [not_and_or, inf_comm, lt_top_iff_ne_top]
  exact or_comm

end Part1

end B5

end CFSG.Quasithin
