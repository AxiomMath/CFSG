module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofG2
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofD4
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofRee
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofSU3
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofSU3KFact
public import CFSG.RankThree.PartTwo.KFacts.K71Item83Sp4
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof

theorem item83_of
    (h82 : Item82Two) (h45 : Sec4.Item4_5) (hcl : Sec4.Inputs47ClassesD4) (hG2 : KF83GTwo)
    (hD4 : KF83TrialityD4) (hRee : KF83ReeF4) : Item83 := by
  intro G _ _ A c L a h hA
  obtain ⟨h81, n, hn, hD | hG | hR | hSp | hU | hS⟩ := h82 G A c L a h hA
  all_goals refine (fun ⟨A₀, d, hd⟩ => ⟨A₀, d, n, hd⟩ :
    (∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n) → _) ?_
  · exact exists_data83_of_trialityD4 hcl hD4 h hn hD
  · exact exists_data83_of_g2 hG2 h hn hG
  · exact exists_data83_of_ree hRee h hn hR
  · exact KFacts.exists_data83_of_sp4 h hn hSp
  · exact KFacts.exists_data83_of_projSU' h hn hU
  · exact exists_data83_of_su3 h45 kF83SUThree h hA h81 hn hS

end CFSG.RankThree.PartTwo.Sec8
