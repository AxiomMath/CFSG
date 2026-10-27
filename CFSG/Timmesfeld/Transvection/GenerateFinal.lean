module

public import CFSG.Timmesfeld.Transvection.FrameLarge
public import CFSG.Timmesfeld.Transvection.ShortRootReg

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

theorem shortRootRegularStatement : ShortRootRegularStatement := by
  intro H _ Δ hyp hml hq A E D E' hP C hC hCD
  have := hyp.finite
  exact hP.exists_conjSub_eq hyp.cls (hyp.cls.noIsolated hyp.points hyp.rank) hyp.points hml
    (hq A hP.memA) hC hCD

theorem transvectionStatementFrameLarge_of_frameImages (h : FrameImagesStatement) :
    TransvectionStatementFrameLarge :=
  transvectionStatementFrameLarge_of_images shortRootRegularStatement h

end CFSG.Timmesfeld.Transvection
