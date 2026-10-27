module

public import CFSG.Quasithin.Background.RonanH154Beta
public import CFSG.Quasithin.Background.RonanH154FTC
public import CFSG.Quasithin.Background.RonanH154Dual
public import CFSG.Quasithin.Background.RonanH154Hyp
public import CFSG.Quasithin.Background.RonanH143NF
public import CFSG.Quasithin.Background.RonanH154Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem std154 :
    Concl154 Rc 0 1 Qstd := by
  have hL : KY mog22plus Qstd ⊓ M22g 0 1 = NQ := by
    rw [KY_Q_L2, M22g_zero_one, NQ2_inf_mog22]
  have hF1 : fixV (rImg Rc (KY mog22plus Qstd)) = X1 := by
    rw [KY_Q_L2]
    exact fixV_NQ2_X1
  have hF2 : fixV (rImg Rc (KY mog22plus Qstd ⊓ M22g 0 1)) = X2 := by
    rw [hL]
    exact fixV_NQ_X2
  obtain ⟨c1, c2, c3, c4⟩ := chain_std_X
  unfold Concl154
  refine ⟨⟨X6, ⟨?_, ?_, ?_, ?_, ?_, c4, rk_X6, dual_std_X, induces_std_X, kernel_std_X⟩,
    ftc_std⟩, hyp3_std, hyp4_std⟩
  · rw [hF1]
    exact c1
  · rw [hF1]
    exact rk_X1
  · rw [hF1, hF2]
    exact c2
  · rw [hF2]
    exact rk_X2
  · rw [hF2]
    exact c3

end CFSG.Quasithin.RonanH154
