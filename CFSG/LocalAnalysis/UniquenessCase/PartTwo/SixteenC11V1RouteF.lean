module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c11_v1_normalizer_le_of_model_rf3 {G : Type} [Group G] [Finite G] (D : Data G)
    (h61 : UC6.R6_1 D) (h1610 : R16_10_2 D) (h169 : R16_9 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (hsig : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))} {J₀ : Subgroup (Vtil V₀ V hV)}
    (hM : S16C11Model (Mbar D.M V₀ V hV) (kBar D.M V₀ V hV L) J₀)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3)
    (hI : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    (hrf : S16C11RF3 L₀ J₀) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hP := hc.setting.hyp16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (barSub V₀ V hV D.T) (Mbar D.M V₀ V hV) :=
    CFSG.ABGLocalTools.isSylowOf_iff.2
      (s16c1_barSub_sylow hMst (TwelveShort.isSylowIn_of_le D D.sylowM.le))
  obtain ⟨Xbar, hXM, hTX, hsolv, hexp, hcount⟩ :=
    s16c11_routeF_data_of_rf3 (s15_Infra_vtil_sq_eq_one V₀ V hV) hM hK hI hT hrf
  exact s16c11_normalizer_le_of_routeF D h61 h1610 h169 hV hc
    (by rw [hsig]; exact Set.mem_singleton 3) hXM hTX hsolv hexp hcount

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
