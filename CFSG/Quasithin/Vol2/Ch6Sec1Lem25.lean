module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Card
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Elim
public import CFSG.Quasithin.H13.NQCatLieOverRank2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Mult

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem stmt6_1_25_of (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact) (kf3 : SmallGroup625Fact)
    (h23 : A23SQTKListFact) (hLie : Lie625Elim) : Stmt6_1_25 := by
  intro G _ _ T M L V n h l hl hlN
  have hI : In625 := ⟨h432, h6111, h6119, h37, h38⟩
  obtain ⟨DL, hDL⟩ := h.toHyp5_0_1.exists_isHall_borel
  obtain ⟨K, hKc, hKq, hKR⟩ :=
    existsComponent6_1_25_of h432 h6110 h6111 h6119 G T M L V n h l hl hlN
  have d : Dat625 T M L V n l DL K := ⟨h, hl, hlN, hDL, hKc, hKq, hKR⟩
  have hn := d.n_eq_two hI kf1 kf2 kf3 h23 hLie
  refine ⟨hn, fun K' hK'c hK'q hK'R => ?_, d.relIndex_E hI kf1 kf2 kf3 h23 hLie hn⟩
  have d' : Dat625 T M L V n l DL K' := ⟨h, hl, hlN, hDL, hK'c, hK'q, hK'R⟩
  exact d'.lieModel_quot hI kf1 kf2 kf3 h23 hLie hn

theorem stmt6_1_25_of_res (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact) (kf3 : SmallGroup625Fact)
    (kf4 : LieOvergroupFact) (h23 : A23SQTKListFact) (hres : Res625Lie) : Stmt6_1_25 :=
  stmt6_1_25_of h432 h6110 h6111 h6119 h37 h38 kf1 kf2 kf3 h23
    (lie625Elim_of kf1 h23 kf4 hres)

theorem stmt6_1_25_of_nqcat
    (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (hE : NQCat.LieOvergroupFactRank2Exc) (h23 : A23SQTKListFact) (hres : Res625Lie) :
    Stmt6_1_25 :=
  stmt6_1_25_of_res h432 h6110 h6111 h6119 h37 h38 kf1 kf2 smallGroup625Fact_holds
    (NQCat.lieOvergroupFact_of NQCat.lieOvergroupFactRank1_holds
      (NQCat.lieOvergroupFactRank2_of hE)) h23 hres

end CFSG.Quasithin.H13
