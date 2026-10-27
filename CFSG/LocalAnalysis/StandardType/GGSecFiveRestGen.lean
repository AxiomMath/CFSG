module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveRestGen (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (Rd Ra : Prop) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧ Rd ∧ Ra

theorem GGSecFiveRestGen.of_local {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) (hO : GGOpAutTrivial p Bs)
    (hI : GGInnerDiagAll p B Bs x L D J) (hT : GGNoTransvection p Bs) :
    GGSecFiveRestGen p B Bs x L D J True True :=
  ⟨hC, hO, hI, hT, trivial, trivial⟩

end CFSG.StandardType

end
