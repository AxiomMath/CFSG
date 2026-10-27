module

public import CFSG.RankThree.PartTwo.Sec17.Item1712Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] noncomputable def Item1711S17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1711 A (lB A)

theorem item1712S17_of (h1711 : Item1711S17) (h7 : Step1712Seven) (hmain : Step1712Main) :
    Item1712S17 :=
  fun G _ _ A c L Y₀ h => rank3II_17_12_of h (h1711 G A c L Y₀ h) (h7 G A c L Y₀ h)
    (hmain G A c L Y₀ h)

end CFSG.RankThree.PartTwo.Sec17
