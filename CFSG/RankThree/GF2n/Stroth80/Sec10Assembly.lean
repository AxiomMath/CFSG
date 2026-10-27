module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth108_of_steps (h101 : Stroth101Statement) (h103a : Stroth103aStatement)
    (h103b : Stroth103bStatement) (h107 : Stroth107Statement)
    (h108 : Stroth108CoreStatement) : Stroth108Statement := by
  intro G _ _ M Q Z B hc n hW hn hnoA2 hgen halt hex
  have H : Sec10Hyp hc n := ⟨hW, hn, hnoA2, hgen, halt, hex⟩
  obtain ⟨hn6, h3⟩ := h107 G M Q Z B hc n H
  obtain rfl : n = 6 := hn6
  obtain ⟨t₀, ht₀⟩ := h101 G M Q Z B hc 6 H
  by_cases h2 : ∃ s : G, Good101 M Q Z B s ∧ SLMNat hc s 2
  · obtain ⟨s, hs, hs2⟩ := h2
    obtain ⟨y, hy, h103⟩ := h103a G M Q Z B hc 6 s H hs hs2
    exact h108 G M Q Z B hc (s * y) H h3 h103
  · have hno2 : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2 := by
      intro s hs hs2
      exact h2 ⟨s, hs, hs2⟩
    exact h108 G M Q Z B hc t₀ H h3 ⟨ht₀, h103b G M Q Z B hc 6 H hno2 t₀ ht₀⟩

end CFSG.RankThree.GF2n.Stroth80
