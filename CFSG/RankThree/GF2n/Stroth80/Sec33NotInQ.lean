module

public import CFSG.RankThree.GF2n.Stroth80.DictB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.B_le_QB (hc : Ctx M Q Z B) : B ≤ QB B := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [(Ctx.QB_eq hc hg).2, hg]
  intro x hx
  rw [mem_conjSubgroup] at hx ⊢
  exact hc.Z_le_Q hx

end CFSG.RankThree.GF2n.Stroth80
