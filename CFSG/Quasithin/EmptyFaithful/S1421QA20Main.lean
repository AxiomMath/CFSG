module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Big
public import CFSG.Quasithin.EmptyFaithful.S1421QA20Lie

public section

namespace CFSG.Quasithin

theorem core3BigExclusion_holds : Core3BigExclusion := by
  intro X _ _ h
  rcases h with ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, -, hf, h⟩
  · exact S1421QA20.a318Exclusion_big_sp4 hf h
  · exact S1421QA20.a318Exclusion_big_g2 hf h
  · exact S1421QA20.a318Exclusion_big_3d4 hf h
  · exact S1421QA20.a318Exclusion_big_2f4 hf h

end CFSG.Quasithin
