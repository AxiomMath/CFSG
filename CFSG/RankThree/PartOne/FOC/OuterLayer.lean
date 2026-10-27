module

public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.TCF.Simple

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec66T (innerAut fixSub)

theorem outerComp_of_fixed_simple_layer {p : ℕ} {T : Type} [Group T] [Finite T]
    (h : ∀ β : MulAut T, β ^ p = 1 → β ∉ innerAut T →
      ∃ N : Subgroup ↥(fixSub β), IsSimpleGroup ↥N ∧ (∃ a b : ↥N, a * b ≠ b * a) ∧
        commutator ↥(fixSub β) ≤ N ∧ ∀ y : ↥(fixSub β), y ^ p = 1 → y ∈ N) :
    OuterComp p T := by
  classical
  intro _ β hβp hβinn _ y hβy hyp E hE
  obtain ⟨N, hNs, hNnc, hcomm, hpow⟩ := h β hβp hβinn
  have hN'F : N.map (fixSub β).subtype ≤ fixSub β := Subgroup.map_subtype_le N
  have hFF : ⁅fixSub β, fixSub β⁆ = (commutator ↥(fixSub β)).map (fixSub β).subtype := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hFN' : ⁅fixSub β, fixSub β⁆ ≤ N.map (fixSub β).subtype := by
    rw [hFF]
    exact Subgroup.map_mono hcomm
  have hns : ¬ Group.IsSolvable ↥N := by
    intro h
    obtain ⟨a, b, hab⟩ := hNnc
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 h a b)
  have hsimple : TCF.SimpleOrBot (N.map (fixSub β).subtype) :=
    TCF.simpleOrBot_of_mulEquiv_simple (G₀ := ↥N) hns
      (Subgroup.equivMapOfInjective N (fixSub β).subtype (fixSub β).subtype_injective)
  have hEN : E = N.map (fixSub β).subtype :=
    TCF.component_eq_of_simpleOrBot hN'F hFN' hsimple hE
  rw [hEN]
  exact ⟨⟨y, hβy⟩, hpow ⟨y, hβy⟩ (Subtype.ext (by simpa using hyp)), rfl⟩

end CFSG.RankThree.PartOne.FOC
