module

public import CFSG.Quasithin.EmptyFaithful.S152He11D
public import CFSG.Quasithin.EmptyFaithful.S152He12G
public import CFSG.Quasithin.EmptyFaithful.S152He12H
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Final
public import CFSG.Quasithin.Background.C1PackS15207
public import CFSG.Quasithin.EmptyFaithful.S151cA3
public import CFSG.Quasithin.EmptyFaithful.S152FinR
public import CFSG.Quasithin.EmptyFaithful.S152He6Final
public import CFSG.Quasithin.EmptyFaithful.S152He7SevenBridge
public import CFSG.Quasithin.EmptyFaithful.S152L01
public import CFSG.Quasithin.EmptyFaithful.S152L08
public import CFSG.Quasithin.EmptyFaithful.S152L25F
public import CFSG.Quasithin.EmptyFaithful.S152N10
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152N2Frob
public import CFSG.Quasithin.EmptyFaithful.S152NPairD
public import CFSG.Quasithin.EmptyFaithful.S152O4Props
public import CFSG.Quasithin.EmptyFaithful.S152QB
public import CFSG.Quasithin.EmptyFaithful.S152QF
public import CFSG.Quasithin.EmptyFaithful.S152U20

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2

theorem stageRankNotTwo_of_basic_inputs_ce25
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
    (hlift : Input15209Lift) (hF : Input15208F112) : StageRankNotTwo := by
  have hInsp24 : Insp15224 :=
    insp15224_of_noA6 hF318 h36 h38 hK.alt6 (insp15224NoA6_of_noF2 hF318 h36 h38 hK hc hno)
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
  have h15204 : StageLemma15204 :=
    He11.stageLemma15204_of_named_noA314 h1515 h1519 h15112 h15201 h15203 h15206 h15207 h37 h38 h39
      h36 h129 hF204 hD204 hB204
  have h15208 : StageLemma15208 := stageLemma15208_of h1519 h15112 h15204 h15206 h15207 hF
  have hex : Input15209Exists := input15209Exists_of_lift h15112 h15208 hlift
  have hord : Input15209Order := input15209Order_of_exists hex
  have h15210 : StageLemma15210 := stageLemma15210_of h1518 h15201
  have h15211 : StageLemma15211 := stageLemma15211_of h15112 h15208 h15210 hord
  have h15209 : StageNotation15209 :=
    stageNotation15209_of_pair h1519 h15112 h15208 hord (stagePair152_of h15112 h15208 hord)
  have hcore : He12.Input15212CoreW :=
    He12.input15212CoreW_of_prop134He h134 hA3 h1416 h15208 h15209 hInsp12 h1519 h122 hF318 h36
      h38 hK
  have h15212 : He12.StageLemma15212W :=
    He12.stageLemma15212W_of_core_ce h1416 h1515 h15201 h5 h1519 h15208 h15209 h15211 hcore
  have h15213 : StageLemma15213 :=
    He12.stageLemma15213W_of h15201 h15209 h15210 h15211 h15212 omega4PlusIsS3xS3 frobenius20IsSz2
  have h15214 : StageLemma15214 :=
    He12.stageLemma15214W_of_ce h15201 h1515 h1518 h1519 h15209 h15211 h15212 h15213
      omega4PlusIsS3xS3 om4Z152
  have h16 : StageLemma15216 := stageLemma15216_of h15214 h15213 h15211 h15209
  have h17 : StageLemma15217 := stageLemma15217_of h15214 h16
  have h18 : StageLemma15218 :=
    stageLemma15218_of h5 h1519 h15211 h15213 h15214 h15209 h16 h17 om4FactsStatement
  have h23 : StageLemma15223 :=
    S15223.stageLemma15223_of_stagesW hC129 hC27 hF318 h36 h37 h38 hK hcover h51 hI16 hA8 kR kL kP kB hA3
      h5 h1519 h15112 h15208 h15211 h15212 h15213 h15214 h15209 h16 h17 h18 h1515 h15201 h15202 h15203
  have h20 : StageLemma15220 :=
    stageLemma15220_of h5 h1519 h15211 h15213 h15214 h15209 h16 h17 h18 h15112
  have h24 : StageLemma15224 := stageLemma15224_of hlist hA3 h15208 h15214 h16 h18 h20 hInsp24
  have htail : He12.Stage15215TailW :=
    He12.stage15215TailW_of_core hlist hA3 h15208 h15209 h16 h18 hcoreW
  have h15215 : StageTheorem15215 :=
    He12.stageTheorem15215W_of h15211 h15212 h15213 h15214 h15209 h20 h23 h24 htail
  have h25 : StageLemma15225 := stageLemma15225_of h15213 h15214 h15215 claim15225F
  exact stageRankNotTwo_of_finalR h1518 h1519 h15111 h15112 h15208 h15209 h15213 h15215 h25
    (stageLemma15226_of h15213 h15214
      (He12.stageLemma15226OneW_of h15209 h15211 h15212 h15213 h15214 h15215))
    (He12.stageLemma15227TwoW_of_good h1519 h15111 h15201 h15208 h15209 h15211 h15212 h15213
      h15214 ⟨insp15227TransLn_of_ii (insp15227TransIi_of_b42 hB42), hHeMod⟩ hParGood
      (insp15227Shape_of_seven_holds (insp15227ShapeSeven_of_b42 hB42)))
    (He12.stageLemma15228W_of h15111 h15212 h15213 h15209 h25) stageFinal152R

end CFSG.Quasithin
