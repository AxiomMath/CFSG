module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57Wire
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223L3NotMc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223JMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223KcMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Final
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Stage22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223

theorem stageLemma15223_of_stagesW
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hcover : AsA36NoOddCover) (h51 : AsB51) (hI16 : AsI16Cover)
    (hA8 : AsI16CoverA8) (kR : Input21Rank) (kL : ThreeRankBlocks) (kP : Input21ProperRank)
    (kB : SolvOvergroupsInBorel) (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (h5 : StageLemma15205) (h159 : StageLemma1519) (h15112 : StageLemma15112)
    (h8 : StageLemma15208) (h11 : StageLemma15211) (h12 : He12.StageLemma15212W)
    (h13 : StageLemma15213) (h14 : StageLemma15214) (hN : StageNotation15209)
    (h16 : StageLemma15216) (h17 : StageLemma15217) (h18 : StageLemma15218)
    (h1515 : StageLemma1515CE) (h15201 : StageLemma15201) (h15202 : StageLemma15202)
    (h15203 : StageLemma15203) : StageLemma15223 := by
  have hIrr : Input15209Irr := input15209Irr_of h8
  have hJ : Input15112J := input15112J_of h15112 h8 hN
  have hKc : Input1210Kc := input1210Kc_of h11 h12 h13 hN
  have h3 : Input15221Three :=
    S15221.input15221Three_of h5 h159 h11 h12 h13 h14 hN h16 h17 h18 h1515 h15201 h15203 h8 hIrr
      hJ hKc
  have h21 : StageLemma15221W :=
    stageLemma15221W_of h5 h159 h8 h11 h12 h13 h14 hN h16 h17 hIrr hJ hKc h3
  have h22 : StageLemma15222Canon :=
    stageLemma15222Canon_of_stages h15202 h1515 h15201 hN h16 h17 h18 h21 h5 h159 h11 h13 h14
  exact stageLemma15223_of_steps h5 h159 h8 h11 h12 h13 h14 hN h16 h17 h18
    (reduction15223P2_of_pieces
      (reduction15223P2A3L2_of h5 h159 h11 h12 h13 h14 hN h16 h17 h18)
      (reduction15223P2A5A7_of h5 h159 h11 h12 h13 h14 hN h16 h17 h18)
      (reduction15223P2NotMc_of h5 h159 h11 h12 h13 h14 hN h16 h17 h18 hOrb))
    (reduction15223P3_of hC129 h5 h17 h18)
    (reduction15223P4_of hC129 hC27 hF318 h36 h37 h38 hK hcover h51 hI16 hA8 kR kL kP kB h5 h159
      h8 h11 h12 h13 h14 hN h16 h17 h18 h21 h22)

end S15223

end CFSG.Quasithin
