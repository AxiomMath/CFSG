module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 calC)

theorem exists_sylow_three_ge_of_le {G : Type} [Group G] [Finite G] {M L Q : Subgroup G}
    (hLM : L ≤ M) (hQ : IsSylowOf 3 Q L) : ∃ P : Subgroup G, IsSylowOf 3 P M ∧ Q ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := (hQ.isPGroup.comap_subtype (K := M)).exists_le_sylow
  exact ⟨S.map M.subtype, ⟨S, rfl⟩, fun x hx => ⟨⟨x, hLM (hQ.le hx)⟩, hS hx, rfl⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
