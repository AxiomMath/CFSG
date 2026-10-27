module

public import CFSG.CharacterTheory.Blocks.CharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.bi_brauer_characterization
    (G : Type) [Group G] [Finite G] (f : G → ℂ) (hf : BlocksIsClassFunction f) :
    f ∈ BlocksVChar G ↔
      ∀ E : Subgroup G, BlocksBrauerElementary E → (fun e : E => f e) ∈ BlocksVChar E := by
  classical
  let := Fintype.ofFinite G
  simpa only [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup,
    blocksBrauerElementary_iff, Function.comp_def, Subgroup.subtype_apply] using
    TwoRankLowerBound.Helpers.brauer_virtual_character_criterion f hf

end CFSG.Open
