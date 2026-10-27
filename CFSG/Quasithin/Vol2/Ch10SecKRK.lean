module

public import CFSG.Quasithin.Vol2.Ch10SecKRKd
public import CFSG.Quasithin.Vol2.Ch10SecKRKe
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases1
public import CFSG.Quasithin.Vol2.Ch10SecKRKc
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem factK1_of (hAC : A312AutCent) : FactK1 := by
  intro Γ _ _ H R J L V₁ hH _ hR hJ hJq hL hLJ hne hRL _ hVL hVel hVn hVc hVcent hVJ hM
  have h : KRK.K1Hyp H R J L V₁ := ⟨hH, hR, hJ, Insp9.isQuasisimple_of_open hJq, hL, hLJ, hne,
    hRL, hVL, hVel, hVn, hVc, hVcent, hVJ⟩
  have hX := h.sqtkHyp_QJ
  rcases hAC (KRK.QJ J) h.quasi_QJ hX.isSQTKCat hX.o2 _ h.sylow_T _ h.lfam_B h.B_ne_top
      h.le_normalizer_B (h.type_B hM) _ h.vB h.vel_V h.B_le_normalizer_V h.comm_V h.V_ne_bot
      h.pCoreOf_B_le h.lift_hyp with hα | ⟨n, hn, F, _, _, hF, ⟨e₁⟩, ⟨e₂⟩⟩
  · left
    rintro r ⟨hrR, hrc⟩
    have hrN := h.mem_normalizer_J hrR hrc
    exact KRK.K1Hyp.mem_centralizer_of_alpha_eq_one h hrN
      (hα _ (KRK.K1Hyp.alpha_fix_B hrN hrc) (KRK.K1Hyp.alpha_T hrN hrR) (h.alpha_pow hrN hrR))
  · right
    exact ⟨n, hn, F, inferInstance, inferInstance, hF, ⟨h.centerEquiv.symm.trans e₁⟩,
      ⟨h.modO2B.symm.trans e₂⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
