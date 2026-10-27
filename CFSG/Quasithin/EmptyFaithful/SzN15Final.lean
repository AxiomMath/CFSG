module

public import CFSG.Quasithin.EmptyFaithful.S153F21B
public import CFSG.Quasithin.EmptyFaithful.SzN5Label
public import CFSG.Quasithin.EmptyFaithful.SzN15Diag
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.EmptyFaithful.SzN4Final

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem stage15313_of_named_stageB_inputs7M3
    (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (h15 : Input15315Two) (h16 : Input15316One) (h36 : Input15336One)
    (kR : Input21Rank) (kP : Input21ProperRank)
    (k17L : ThreeRankBlocks) (k17B : SolvOvergroupsThreePrime) (k17T : ThetaEqComponent)
    (k18S : Lin2Setup) (k18R : Lin2RLSylow) (kZ : Lin2ZLInYL)
    (k19C : Lin2QuotIsLin2OrA5) (k19A : A5Setup) (k19F : A5FixedPoints) (k19O : A5OddCommuting)
    (k20N : SL3Sp4NotA38Type) (k20A : SzN15.NoGraphAutOnFFModule3) (k20B : SolvOvergroupsInBorel)
    (k20C : RankTwoMaxParabolics)
    (k21N : A7NotA38Type) (k21T : HatA6ProperThreePart) (k21E : ExcA7NoS3Section)
    (k21O : OrdA7ConfigNoNine) (k21V : HatA6VleU) (k21S : HatA6SwapLocal)
    (h23 : Input15323) (h24 : Input15324M) : Stage15313 :=
  theorem15313_of_stages_min h11 h113 hC27 hA37 hA38 hcover h15 h16
    (S153F.input15317_of_named_inputs hcover kR k17L k17B k17T)
    (input15318_of_kL h113 hA37 hA38 k18S (lin2YLLabel_of_RL h113 k18S k18R) kZ)
    (S153F.input15319_of_named_inputs h113 hA37 hA38 k19C k19A k19F
      k19O (v2CommutatorYp_holds h113))
    (S153F.input15320M_of_named_inputs3 hA37 hA38 k20N k20A k20B k20C)
    (S153D.input15321_of_kernels hcover kR kP
      (S153F.input15321Rest_of_named_inputs hcover hA37 hA38 kR h36 k21N k21T k21E k21O
        (S153F.hatA6Endgame_of_named_inputs h113 k21V k21S)))
    h23 h24

end CFSG.Quasithin
