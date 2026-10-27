module

public import CFSG.Milestones.ASVolI.C41.BigCase3
public import CFSG.Quasithin.Background.C41PfJ
public import CFSG.Quasithin.Background.C41PfS
public import CFSG.Quasithin.Background.C41PfU
public import CFSG.Quasithin.Background.C41PfZ
public import CFSG.Quasithin.Background.C41PfK
public import CFSG.Quasithin.H13.L32NA3SQTK
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.Background.Asc82Holds
public import CFSG.Quasithin.Vol2.KGFactLem1211G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C41Pf

variable {G : Type} [Group G] [Finite G]

theorem burnsideC41w_c41InspG_of_big (hK0 : C41KZero G) (hA3 : A3Orbits G)
    (h134 : MS93.burnsideC134w_AS_C_1_34_corrBig) : C41InspG G := by
  intro H R M L V K hP h1 _ hc
  obtain ⟨n, F, iF, fF, hn, hF, he, hMS, hcase, hmax, hpsl, hline⟩ :=
    burnsideC41w_c47_case3_big h134 hP h1 hc
  have hc3 : C41Case3 H R M L V K :=
    ⟨n, F, iF, fF, hn, hF, he, hMS,
      hcase.imp_right (Or.imp_right (Or.imp_right isC134Case4Corr_local_iff.mpr)), hmax, hpsl,
      hline⟩
  exact c41Conclusion_of_case hK0 hA3 hP (SBc6.isSimpleGroup_of_psl hn hpsl)
    (Or.inr (Or.inr (Or.inl hc3)))

theorem burnsideC41w_asc41Statement_of_big
    (hC27 : ASC27Statement G) (h134 : MS93.burnsideC134w_AS_C_1_34_corrBig) : ASC41Statement G :=
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1
  have hK0 : C41KZero G :=
    c41KZero_of hC27 H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1 H13.KGG2.lem1211NNG2_holds
  asc41Statement_of asc82Thm2_holds H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1
    (fun _ _ hX => Vol2Native.L122A.isSimpleGroup_of_a38Types hX) (H13.VolI.asc129Statement_holds G)
    (asc111Statement_holds G) (asc19Statement_holds G) hC27 c41KGBorel_holds
    (c41ProjStep_of hA3 (fun K hK hq => outSolvable_of_isSQTKIn K hK hq) hK0)
    (c41Elim_of H13.KGG2.lem1211NNG2_holds) (c41InspB_of hK0 hA3 c46Block_holds)
    (c41InspE_of hK0 hA3 c41Sp4Block_holds) (burnsideC41w_c41InspG_of_big hK0 hA3 h134) (c41InspH_of hK0 hA3)

end C41Pf

end CFSG.Quasithin
