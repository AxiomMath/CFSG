module

public import CFSG.RankThree.PartTwo.KFacts.KS14OrdersSpor
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds
public import CFSG.RankThree.PartTwo.Sec4.Item422Holds
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLePtRoute

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec11

theorem step155HostE0WRes1TypeFBarNotLe_a7_gen
    (h316 : Sec19.Item316)
    (h148HJ : Item148HJS14) (P : ∀ (Y : Type) [Group Y], Prop) :
    Step155HostE0WRes1TypeFBarNotLe (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  step155HostE0WRes1TypeFBarNotLe_of_in Sec14.Ronan149.item149S14_holds
    (fun G _ _ A c L hR hq hN hS X K Y M T P' hC _hmax _hab _hE _h146 _hRP _hIX Yc _hAt
      _hYsimple _hP _hEA _hEO _hcomm _hfield hLX =>
      res1L112InAt_a7 Sec14.Ronan148M.concl142S14_holds Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item145BotS14_holds
        (Sec14.item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
        Sec13.rank3II_13_1_holds
        (Sec13.rank3II_13_3_of Sec13.rank3II_13_1_holds CFSG.RankThree.PartTwo.item4_22_holds
          Sec4.rank3II_4_5)
        (Sec13.item13SetupAt_of CFSG.RankThree.PartTwo.item4_22_holds Sec4.rank3II_4_5)
        (Res1PtInputs.item153Main_at h316 Sec14.Ronan149.item149S14_holds
          Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
          CFSG.RankThree.PartTwo.item135_holds Sec13.Ronan137H.item137_holds
          CFSG.RankThree.PartTwo.item142AllS14_holds Close.closed_sec4Item4_8
          Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
          Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
          Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds h148HJ hR
          (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
            hR
            (Proof15Res6.not_allPointsHJ_of_isEmpty hS
              (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inl hq))))
            (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
              Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
              Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hR)))
        (item1411_1R_of claim1411LocalR_holds G A c L hR)
        CFSG.RankThree.PartTwo.item135_holds hR hq hN hS hC hLX)

theorem step155HostE0WRes1TypeFBarNotLe_m22_gen
    (h316 : Sec19.Item316)
    (h148HJ : Item148HJS14) (h159 : Item159R) (P : ∀ (Y : Type) [Group Y], Prop) :
    Step155HostE0WRes1TypeFBarNotLe (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      P :=
  step155HostE0WRes1TypeFBarNotLe_of_in Sec14.Ronan149.item149S14_holds
    (fun G _ _ A c L hR hq hN hS X K Y M T P' hC _hmax _hab _hE _h146 _hRP _hIX Yc _hAt
      _hYsimple _hP _hEA _hEO _hcomm _hfield hLX =>
      res1L112InAt_m22 Sec14.Ronan148M.concl142S14_holds Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item145BotS14_holds
        (Sec14.item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
        Sec13.rank3II_13_1_holds
        (Sec13.rank3II_13_3_of Sec13.rank3II_13_1_holds CFSG.RankThree.PartTwo.item4_22_holds
          Sec4.rank3II_4_5)
        (Sec13.item13SetupAt_of CFSG.RankThree.PartTwo.item4_22_holds Sec4.rank3II_4_5)
        (rank3II_15_12_of_main Sec13.rank3II_13_1_holds Sec13.sporadicModels131 Sec13.slTwoCenter
          (fun p e _ => KFacts.KS14.not_isoLThreePi_M22 p e)
          (fun p f _ => KFacts.KS14.not_isLThreeEpsAt_M22 p f)
          KFacts.KS14.isEmpty_mulEquiv_M22_alternating.2.1 KFacts.KS14.isEmpty_mulEquiv_M22_M12
          KFacts.KS14.isEmpty_mulEquiv_M22_J2 CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
          (ks15M22Gen_of_items Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item145BotS14_holds
            (Sec14.item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
            Sec13.rank3II_13_1_holds CFSG.RankThree.PartTwo.item134_holds
            Close.closed_sec4Item4_8 CFSG.RankThree.PartTwo.item135_holds)
          hR (h159 G A c L hR) (item1411_1R_of claim1411LocalR_holds G A c L hR)
          (Res1PtInputs.item153Main_at h316 Sec14.Ronan149.item149S14_holds
            Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
            CFSG.RankThree.PartTwo.item135_holds Sec13.Ronan137H.item137_holds
            CFSG.RankThree.PartTwo.item142AllS14_holds Close.closed_sec4Item4_8
            Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
            Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
            Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds h148HJ hR
            (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds
              Close.closed_sec4Item4_8 hR
              (Proof15Res6.not_allPointsHJ_of_isEmpty hS
                (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inr hq))))
              (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
                Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
                Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hR)))
          (Res1PtInputs.claim153Obs_at Sec14.Ronan148M.item148R_holds
            Sec14.Ronan149.item149S14_holds hR
            (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds
              Close.closed_sec4Item4_8 hR
              (Proof15Res6.not_allPointsHJ_of_isEmpty hS
                (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inr hq))))
              (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
                Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
                Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hR))))
        (step142LowerGenM22_of Sec13.rank3II_13_1_holds) hR hq hN hS hC hLX)

theorem step155HostE0WRes1TypeFBar_a7_of_zExcl
    (h316 : Sec19.Item316)
    (h148HJ : Item148HJS14) {P : ∀ (Y : Type) [Group Y], Prop}
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P) :
    Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  step155HostE0WRes1TypeFBar_of_le
    (step155HostE0WRes1TypeFBarLe_a7_of_zExclNRoute h316 Sec13.rank3II_13_1_holds
      (Sec13.rank3II_13_3_of Sec13.rank3II_13_1_holds CFSG.RankThree.PartTwo.item4_22_holds
        Sec4.rank3II_4_5)
      (Sec13.item13SetupAt_of CFSG.RankThree.PartTwo.item4_22_holds Sec4.rank3II_4_5)
      CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
      Sec13.Ronan137H.item137_holds
      (Sec14.item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
      CFSG.RankThree.PartTwo.item142AllS14_holds Sec14.Ronan148M.concl142S14_holds
      Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
      Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
      Sec14.Ronan148M.item148R_holds h148HJ Sec14.Ronan149.item149S14_holds
      Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz hz)
    (step155HostE0WRes1TypeFBarNotLe_a7_gen h316 h148HJ P)

theorem step155HostE0WRes1TypeFBar_m22_of_zExcl
    (h316 : Sec19.Item316)
    (h148HJ : Item148HJS14) (h159 : Item159R) {P : ∀ (Y : Type) [Group Y], Prop}
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P :=
  step155HostE0WRes1TypeFBar_of_le
    (step155HostE0WRes1TypeFBarLe_m22_of_zExclNRoute h316 Sec13.rank3II_13_1_holds
      (Sec13.rank3II_13_3_of Sec13.rank3II_13_1_holds CFSG.RankThree.PartTwo.item4_22_holds
        Sec4.rank3II_4_5)
      (Sec13.item13SetupAt_of CFSG.RankThree.PartTwo.item4_22_holds Sec4.rank3II_4_5)
      CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
      Sec13.Ronan137H.item137_holds
      (Sec14.item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
      CFSG.RankThree.PartTwo.item142AllS14_holds Sec14.Ronan148M.concl142S14_holds
      Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
      Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
      Sec14.Ronan148M.item148R_holds h148HJ Sec14.Ronan149.item149S14_holds
      Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz
      (step142LowerGenM22_of Sec13.rank3II_13_1_holds) hz)
    (step155HostE0WRes1TypeFBarNotLe_m22_gen h316 h148HJ h159 P)

end CFSG.RankThree.PartTwo.Sec15
