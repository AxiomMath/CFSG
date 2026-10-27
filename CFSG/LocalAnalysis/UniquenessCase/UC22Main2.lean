module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

structure Steps0 (D : Data G) (Ch : Choice2011 G) : Prop where
  s20_4 : S20_4 D
  s20_10 : S20_10 D
  ch : ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
    ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
      AlphaCond D.T B0 n ∧ B0 ≤ D.M
  s22_2 : S22_2 D Ch
  s22_end : S22_end D Ch

theorem uc22_isTI_of_steps0 (D : Data G) (Ch : Choice2011 G) (hne : (hSet D.T D.M).Nonempty)
    (h1930 : H1930 D) (h : Steps0 D Ch) : CFSG.CGT.Timmesfeld75.IsTI D.U :=
  uc22_isTI_of_steps D Ch hne h1930 h.s20_4 h.s20_10 h.ch h.s22_2 h.s22_end

end CFSG.LocalAnalysis.UniquenessCase.UC22
