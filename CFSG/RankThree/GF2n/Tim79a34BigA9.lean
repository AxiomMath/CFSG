module

public import CFSG.RankThree.GF2n.Tim79a34BigEnd
public import CFSG.RankThree.GF2n.Tim79a34A9Core

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint

theorem bigA9Statement_of_data (hI : A9AbsIrrStatement) (hD : BigA9DataStatement) :
    BigA9Statement := by
  intro G _ _ M V Q P H hH hA9
  obtain ⟨L, U, A, _, _, _, _, _, _, _, e, ρ, ρA, κ, hρ, hU, hA, hκ, hspan⟩ :=
    hD G M V Q P H hH hA9
  exact no_A9_of_equivariant_pairing hI e ρ hρ hU hA ρA κ hκ hspan

end CFSG.RankThree.GF2n.Tim79a
