module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameCoord
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly
open scoped Matrix

@[expose] def stdE0 : Fin 5 → ZMod 3 := Pi.single 0 1

@[expose] def stdPhi (c : Fin 5 → ZMod 3) : Finset (Fin 5 → ZMod 3) :=
  Finset.univ.filter fun r => r ⬝ᵥ r = 2 ∧ r 0 = 0 ∧ r ⬝ᵥ c = 0

abbrev stdGood (c : Fin 5 → ZMod 3) : Prop :=
  c 1 ≠ 0 ∨ c 2 ≠ 0 ∨ c 3 ≠ 0 ∨ c 4 ≠ 0

@[expose] def stdGoodSet : Finset (Fin 5 → ZMod 3) :=
  Finset.univ.filter fun c => stdGood c ∧ 12 ≤ (stdPhi c).card

theorem mem_stdGoodSet (c : Fin 5 → ZMod 3) (hc : stdGood c) (h12 : 12 ≤ (stdPhi c).card) :
    c ∈ stdGoodSet := by
  rw [stdGoodSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ c, hc, h12⟩

open scoped CFSG.Decide.Bounded in
theorem stdPhi_card_set : ∀ c ∈ stdGoodSet, (stdPhi c).card = 12 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdPhi_perp_set :
    ∀ c ∈ stdGoodSet, ∀ u : Fin 5 → ZMod 3, (∀ r ∈ stdPhi c, r ⬝ᵥ u = 0) →
      ∃ a b : ZMod 3, u = a • stdE0 + b • c := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdPhi_third_set :
    ∀ c ∈ stdGoodSet, ∀ r ∈ stdPhi c, ∃ w ∈ stdPhi c, w ≠ r ∧ w ≠ -r ∧ r ⬝ᵥ w ≠ 0 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem stdPhi_line_set :
    ∀ c ∈ stdGoodSet, ∀ a b : ZMod 3, b ≠ 0 →
      (((a • stdE0 + b • c) 0 ≠ 0 ∧ (a • stdE0 + b • c) ⬝ᵥ (a • stdE0 + b • c) = 2) ∨
        ((a • stdE0 + b • c) 0 = 0 ∧ (a • stdE0 + b • c) ⬝ᵥ (a • stdE0 + b • c) = 1)) := by
  decide +kernel

end CFSG.StandardType.E6QTwo

end
