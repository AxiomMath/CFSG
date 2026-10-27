module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem k335_exists_sylow_le_range {X : Type} [Group X] {M : Type*} [Group M] {H : Subgroup M}
    {S : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤) {w : X}
    (hSw : S ≤ Subgroup.centralizer ({w} : Set X))
    (e : ↥(Subgroup.centralizer ({w} : Set X)) ≃* ↥H) :
    ∃ φ : ↥H →* X, Function.Injective φ ∧
      ∃ S' : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S' ⊤ ∧ S' ≤ φ.range := by
  refine ⟨(Subgroup.centralizer ({w} : Set X)).subtype.comp e.symm.toMonoidHom, ?_, S, hS,
    fun s hs => ⟨e ⟨s, hSw hs⟩, by simp⟩⟩
  exact (Subgroup.centralizer ({w} : Set X)).subtype_injective.comp e.symm.injective

theorem k335_isSylowOf_top {X : Type} [Group X] [Finite X] (S : Sylow 3 X) :
    CFSG.ABGLocalTools.IsSylowOf 3 (S : Subgroup X) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
