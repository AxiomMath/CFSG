module

public import CFSG.Timmesfeld.Transvection.GenerateFinal
public import CFSG.Timmesfeld.Transvection.GenerateFrameMain

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

theorem frameImagesStatement : FrameImagesStatement := by
  intro H _ Δ hyp hml f hf hcard r hr P Q hfr
  have := hyp.finite
  exact (hfr.toIsMaxFrame hyp.cls).exists_relations_hasFrameImages hyp.cls hyp.points
    (hyp.cls.noIsolated hyp.points hyp.rank) hml (thickLines_of_meetsLines hyp.cls hyp.center hml)
    hf hcard hr

theorem transvectionStatementFrameLarge : TransvectionStatementFrameLarge :=
  transvectionStatementFrameLarge_of_frameImages frameImagesStatement

end CFSG.Timmesfeld.Transvection
