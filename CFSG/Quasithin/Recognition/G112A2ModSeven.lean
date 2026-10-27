module

public import CFSG.Quasithin.Recognition.G112A2ModSevenGlue
public import CFSG.Quasithin.Recognition.G112A2ModStmts

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG

theorem g112A2OpenConcl7_holds : G112A2OpenConcl7 := by
  unfold G112A2OpenConcl7
  intro V _ _ _ B Γ v₁ W X X₀ hH hc
  obtain ⟨hdim, hF, -⟩ := hc
  unfold A2ClauseAt
  intro t ht hr _ hv
  exact (g112A2Seven_glue_false B Γ hF hdim (fun γ hγ v w => hH.isometry γ hγ v w)
    (fun v hv' => hH.nondegenerate v hv') t (hH.X_le ht) hr hv).elim

end CFSG.Quasithin.G112A2
