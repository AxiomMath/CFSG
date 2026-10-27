module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPThreeA
public import CFSG.LocalAnalysis.StandardType.GGQTwoPThreeB
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem ggQTwo_p_eq_three {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer L Bs) (hrc : r ∈ ggCoxRefl M e)
    (h6 : Nat.card (ggRankOneIn L Bs r) = 6) : p = 3 := by
  have hp : p.Prime := hcfg.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.1.1.2.2.2.2.2.1.2.1
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrc
  have hdiv : p ∣ Nat.card (MulAut ↥(ggRankOneIn L Bs r)) :=
    QTwo.p_dvd_card_mulAut_rankOne hcfg hr hrefl
  have hprime := QTwo.prime_dvd_card_mulAut_of_card_six (S := ↥(ggRankOneIn L Bs r)) h6 hp hdiv
  rcases hprime with h2 | h3
  · exact absurd h2 hp2
  · exact h3

end CFSG.StandardType

end
