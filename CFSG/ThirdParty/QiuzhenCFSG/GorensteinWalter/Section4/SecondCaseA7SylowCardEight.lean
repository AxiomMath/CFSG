module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KleinBranch
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinBranchSylowCard

namespace CFSG
end CFSG
open CFSG

/-! # The Sylow-two order in the A7 second case -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch of the second case, the distinguished Sylow
`2`-subgroup has order eight. -/
public theorem secondCase_a7_S_card_eq_eight
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card (↑(c.S : Subgroup G)) = 8 := by
  obtain ⟨hklein, hq⟩ := secondCase_a7_klein_branch
    hmin c w d hA7 hmodel
  exact sylow_card_eight_of_klein_twoCore_and_d6_quotient c hklein hq

end CFSG.GorensteinWalter
