module

public import CFSG.Quasithin.H13.QTH13Slot11C132
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspM22
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBFinal
public import CFSG.Quasithin.Vol2.GoldschmidtA128
public import CFSG.Quasithin.Vol2.KGFactC31KG443
public import CFSG.Quasithin.Vol2.KGFactC31NoM22Of
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKTop
public import CFSG.Quasithin.Vol2.Ch4Sec2T425Inp
public import CFSG.Yardstones.M64f425cd8476.Definitions
public import CFSG.Quasithin.Vol2.Ch4Sec3WFinal432R
public import CFSG.Quasithin.H13.QTH13SlotBig
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXF
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXWire
public import CFSG.Quasithin.Vol2.KGFactC31LieSylFinal
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFMain
public import CFSG.Quasithin.Vol2.KGFactJ4GenL52Gen
public import CFSG.Quasithin.Vol2.Ch4Sec4Prime443Produce
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeAssembly
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4W2

public section

namespace CFSG.Quasithin.H13

theorem ys02_of_holds :
    CFSG.Yardstones.M64f425cd8476.Chapter4Theorems := by
  have hJ4TL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW := CFSG.ASVolI.burnsideJ4KW_twoLocals_holds
  have h32 := CFSG.Quasithin.H13.asC132_holds
  have hb := CFSG.Quasithin.H13.SlotLeaves.burnsideC134w_corrBig_holds
  have hA36 := CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
  have hA37 := CFSG.Quasithin.a37ForSQTK_proved
  have hA38 := CFSG.Quasithin.a38ForSQTK_proved
  have hA39 := CFSG.Quasithin.a39ForSQTK_proved
  have hC27 := CFSG.Quasithin.asc27Statement_of_c132 h32
  have h48 := CFSG.Quasithin.H13.SlotLeaves.asc48Statement_forall_of_big h32 hb hJ4TL
  have h22 := CFSG.Quasithin.asc22Three_of_a37 hA37
  have h425 := CFSG.Quasithin.H13.Ch4.thm4_2_5_of_c27 hC27
  have hNoBig := CFSG.Quasithin.H13.Ch4.NSB.conf4212NoSumBig_holds h22 hC27 hA36 hA37 hA38
    hA39 h425 h48 CFSG.Quasithin.B5.asB51_holds CFSG.Quasithin.asI16Cover_of
    CFSG.Quasithin.asI16CoverA8_of
  have hCRK := CFSG.Quasithin.H13.Ch4.CentK.conf4212CentKND_of hA36 hA37 hA38 hA39 h48 h425
  have hNoSum2 := CFSG.Quasithin.H13.Ch4.CentK.conf4212NoSum2ND_of hA37 hA38 hA39 hCRK
  have hBlk := CFSG.Quasithin.H13.Ch4.J4Blk.j4BlockFacts_of_tl hJ4TL
  have hNC := CFSG.Quasithin.H13.Ch4.J4NSD.j4L5BlockNotSelfDual_of_tl hJ4TL
  have hOut := CFSG.Quasithin.H13.Ch4.j4OutTrivial_holds
  have hKX6 := CFSG.Quasithin.H13.Ch4.j4KXNormal6_of hA36 hA37 hA38 hA39 h48 h425
    CFSG.Quasithin.H13.Ch4.inspBM22Cover_holds
    CFSG.QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
    CFSG.Quasithin.C129Native.a38ForSQTKCat_proved
  have hJ4 := CFSG.Quasithin.H13.Ch4.NoJ4.conf4212NoJ4_of6 hA37 hA38 hA39 hOut hBlk hNC hKX6
  have hKGg := CFSG.Quasithin.H13.Ch4.G2Ru.kgG2BlockRu_holds
  have hKGr := CFSG.Quasithin.H13.Ch4.G2Ru.kgG2BlockRuFF_holds
  have hInspC31 := KGC31.inspC31Sporadic_of KGC31.Ru.inspC31SporadicAt_ru
      (KGC31.J4.inspC31SporadicAtJ_j4 hJ4TL CFSG.Quasithin.J4M4Card.card_M4)
  have hC41 := CFSG.Quasithin.H13.SlotLeaves.asc41Statement_forall_of_big h32 hb
  have hSum : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.C48SumBound G := fun G _ _ =>
    CFSG.Quasithin.C48.c48SumBound_of
      (CFSG.Quasithin.C31.asc31Statement_of_open (hC41 G) hInspC31 CFSG.Quasithin.C35Pf.inspC35_holds)
      (hC41 G)
      (CFSG.Quasithin.C48Spor.c48SporStep_of (G := G)
        (CFSG.Quasithin.C22Pf.asc22One_of (G := G) hA37) hInspC31
        (CFSG.Quasithin.C48Cover.c48SporCoverFact_holds (G := G)))
      (CFSG.Quasithin.C48Pf.c48C41FourStep_of (G := G)
        (CFSG.Quasithin.C22Pf.asc22Three_of (G := G) hA37) (hC27 G)
        CFSG.Quasithin.B5.asB51_holds CFSG.Quasithin.asI16Cover_of
        CFSG.Quasithin.asI16CoverA8_of CFSG.Quasithin.C48Pf.fourModFact_holds)
      (CFSG.Quasithin.H13.VolI.asc129Statement_holds G) (CFSG.Quasithin.asc19Statement_holds G)
  have h4213 := CFSG.Quasithin.H13.Ch4.stmt4_2_13FF_of_open_centk h48 hSum hNoBig hC27 hKGg hKGr hNoSum2 hJ4
  have h432 := CFSG.Quasithin.H13.Ch4.stmt4_3_2_of_restW
      (SlotLeaves.asc48Statement_forall_of_big h32 hb hJ4TL)
      CFSG.Quasithin.H13.Ch4.I436.insp436M22M23_holds hb
      (CFSG.Quasithin.H13.Ch4.gap437Sp4Z_of CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds
          (CFSG.Quasithin.H13.Ch4.lemmaC53C56Six_of CFSG.Quasithin.theoremC126_proved
              (CFSG.Quasithin.C58NS.MPB.minParabolicBlockSubnormal_holds
                  (CFSG.QuasithinUnique.Bridge.asB113_of_timmesfeld CFSG.Quasithin.B15P4.asB15Part4)))
          (CFSG.Quasithin.a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
          (CFSG.Quasithin.a38ForSQTK_of_cat CFSG.Quasithin.C129Native.a38ForSQTKCat_proved)
          (CFSG.Quasithin.a39ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved))
  have hA134 := CFSG.SectionRank.QTK.CentreFact.a134Fact_holds
  have hA21 := CFSG.Quasithin.asA21SQTKSection
  have h128 := CFSG.Quasithin.ASInputs.as_A_1_28_holds
  have hExcRes := CFSG.Quasithin.KGC31.noM22SectionLieExcRes_of_lieSylow11
    CFSG.Quasithin.KGC31.lieSylow11Exc_holds
  have hExc := CFSG.Quasithin.KGC31.noM22SectionLieExc_of_res hExcRes
  have hLie := CFSG.Quasithin.KGC31.NoM22.noM22SectionLie_of hExc
  have hLoc := CFSG.Quasithin.KGC31.KG443.kg443J4Loc_holds hLie
  have hGenL := CFSG.Quasithin.H13.Ch4.G443J4.kg443J4GenL52_holds_gen hJ4TL
  have hGap := CFSG.Quasithin.H13.Ch4.G443J4.gap443J4_of' hA39 hA21 hLoc hGenL
  exact ⟨h4213, h432, CFSG.Quasithin.H13.Ch4.stmt4_4_3Orbit'_of_insp443List h4213 h128 hA134 hGap
    CFSG.SectionRank.QTK.Insp443.insp443List'_holds⟩

end CFSG.Quasithin.H13

end
