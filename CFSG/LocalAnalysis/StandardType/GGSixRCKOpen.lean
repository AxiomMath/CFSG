module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRest
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33InnCoprime
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33JRow

public section

namespace CFSG.StandardType

@[expose] def GGSixRootCommKnownOpen :
    Prop :=
  ∀ i : GGSixRCKRow, i ≠ .L32 → i ≠ .U33 → GGSixRootCommKnownRow i

theorem ggSixRootCommKnownRest_of_open
    (h : GGSixRootCommKnownOpen) : GGSixRootCommKnownRest := by
  intro i hi
  by_cases hu : i = .U33
  · subst hu
    intro X _ _ t n f ψ p G₀ A B₁ D J L hrow _ _ hp hp2 hA hBA hDB hD _ _ hBN hBC h4 _ _ _ hBL hmkL
      _ _ _ hLx hDL hJL _
    exact absurd hrow (RCKU33.not_jRow_U33 RCKU33.ggInnCoprimeRankInput hp hp2 hA hBA hDB hD hBC h4
      hBL hmkL hLx hDL hJL)
  · exact h i hi hu

theorem ggSixRootCommKnown_of_open
    (h : GGSixRootCommKnownOpen) : GGSixRootCommKnown :=
  ggSixRootCommKnown_of_rest (ggSixRootCommKnownRest_of_open h)

end CFSG.StandardType
