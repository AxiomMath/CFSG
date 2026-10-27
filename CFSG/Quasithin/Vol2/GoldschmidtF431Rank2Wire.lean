module

public import CFSG.Quasithin.Vol2.Ch5Sec3PerType
import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutModel
import CFSG.Quasithin.Vol2.GoldschmidtF48RigFinal
import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Complete

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem f431Rank2At_psl3 : F431Rank2At .PSL 3 := by
  intro G _ _ hG hnab M₁ M₂ f hP hyps
  have hm : F431ModelFacts .PSL 3 f := f431ModelFacts_psl3 f
  have h45 : F431Facts45 .PSL 3 f hm := f431Facts45_psl f hm
  have hrec : F431Recognition .PSL 3 f :=
    recognition_of_facts hm (f431Generation_psl3 f) (polyNumber .PSL) (three_le_polyNumber _) h45
      (f431F48_psl f hP.1 hm)
  obtain ⟨D, _, hD, hext⟩ := hyps.1
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hext
  exact f431_of_card_le hrec G hG hnab M₁ M₂ D hD E
    (f431L3Order_of_inputs hP.1 hm h45 (f431Out_psl3 hP.1) (f431L3Lie f) G hG hnab M₁ M₂ hyps D
      hD E)

theorem f431Rank2At_psp : F431Rank2At .PSp 2 := by
  intro G _ _ hG hnab M₁ M₂ f hP hyps
  have hm : F431ModelFacts .PSp 2 f := f431ModelFacts_psp f
  have hrec : F431Recognition .PSp 2 f :=
    recognition_of_facts hm (f431Generation_psp f) (polyNumber .PSp) (three_le_polyNumber _)
      (f431Facts45_psp f hm) (f431F48_psp f hP.1 hm)
  exact f431_sp_of_inputs hrec (f431Out_psp f hP) (f431SpLocal_psp f) G hG hnab M₁ M₂ hyps

end CFSG.Quasithin.H13.F431
