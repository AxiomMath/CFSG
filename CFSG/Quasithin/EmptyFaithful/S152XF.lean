module

public import CFSG.Quasithin.EmptyFaithful.S152He12I
public import CFSG.Quasithin.EmptyFaithful.S152XD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2

theorem stageRankNotTwo_of_basic_inputs_ce26
    (hB42 : AsB42)
    (h113 : StageLemma14113) (h1416 : StageLemma1416)
    (h1515 : StageLemma1515CE) (h157 : StageLemma1517) (h1518 : StageLemma1518)
    (h1519 : StageLemma1519) (h15111 : StageLemma15111) (h15112 : StageLemma15112)
    (h15113 : StageLemma15113) (h15114 : StageLemma15114) (h15115 : StageTheorem15115)
    (hF204 : He9.Input15204F112) (hD204 : He9.Input15204Dichotomy)
    (hB204 : He9.Input15204BranchB)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (hlist : Lemma115_3_List)
    (hInsp12 : Insp15212) (h122 : Lemma122A)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (hcover : AsA36NoOddCover)
    (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (kR : Input21Rank) (kL : ThreeRankBlocks)
    (kP : Input21ProperRank) (kB : SolvOvergroupsInBorel)
    (hno : Insp15224NoF2) (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hc : Cent3RankF2)
    (hcoreW : He12.Tail15215CoreW) (hHeMod : HeNoSmallCommutatorModule)
    (hParGood : Insp15227ParGood)
    (hlift : Input15209Lift) (hFr : Input15208F112Rest) : StageRankNotTwo := by
  have h15201 : StageLemma15201 := stageLemma15201_of h157 h15115
  have h15202 : StageLemma15202 := stageLemma15202_of_ce h1515 h1519
  have h15203 : StageLemma15203 :=
    stageLemma15203_of_ce h113 h1515 h15113 h15114 h15201 h15202 om4IsoStatement
  have hHard : Input15205Hard :=
    C1Pack5.input15205Hard_of_ce h113 h1515 h15201 h15202 h15203 om4IsoStatement
  have h5 : StageLemma15205 := stageLemma15205_of hHard
  have h15206 : StageLemma15206 :=
    stageLemma15206_of_ce frobenius20IsSz2 h1515 h15201 h15203 h5 om4IsoStatement
  have h15207 : StageLemma15207 := stageLemma15207_of_15203 h15203
  exact stageRankNotTwo_of_basic_inputs_ce25 hB42 h113 h1416 h1515 h157 h1518 h1519 h15111 h15112
    h15113 h15114 h15115 hF204 hD204 hB204 h129 h37 h39 h134 hA3 hlist hInsp12 h122 hC129 hC27 hcover h51 hI16 hA8 kR kL kP kB hno hF318
    h36 h38 hK hc hcoreW hHeMod hParGood hlift
    (input15208F112_of_rest h1515 h1519 h15206 h15207 hF204 hFr)

end CFSG.Quasithin
