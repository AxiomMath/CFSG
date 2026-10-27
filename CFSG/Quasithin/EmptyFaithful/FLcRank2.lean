module

public import CFSG.Quasithin.EmptyFaithful.FLcP0
public import CFSG.Quasithin.Background.FLcR2C
public import CFSG.Quasithin.Background.FLcR2A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem input15129Rank2_holds : Input15129Rank2 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have hn : n = 4 ∨ n = 5 := hF.n_eq
  have h4 : 4 ≤ n := by rcases hn with h | h <;> omega
  exact ⟨D.rank2_a h4, D.rank2_b hn, perfectCore_eq_self_of_perfect (D.rank2_c hn)⟩

end CFSG.Quasithin
