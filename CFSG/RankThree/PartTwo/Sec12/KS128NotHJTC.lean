module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJM12
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem ks128NotHJTC_of
    (h45 : Sec4.Item4_5) : KS128NotHJTC := by
  intro h125 G _ _ A c L h hAE hty a ha _ K hK hcK
  exact ⟨fun ⟨_, _, x, hxA, _, hx⟩ =>
      KS128NotHJTC.false_of_pgl h45 h125 h hAE hty ha hK hcK hxA hx,
    fun ⟨⟨φ⟩, _⟩ => KS128NotHJTC.false_of_m12 h45 h125 h hAE hty ha hK hcK φ⟩

section Unconditional

theorem ks128NotHJTC
    : KS128NotHJTC :=
  ks128NotHJTC_of Sec4.rank3II_4_5

end Unconditional

end CFSG.RankThree.PartTwo.Sec12
