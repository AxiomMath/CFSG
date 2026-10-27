module

public import CFSG.Quasithin.H13.F112DSAL2Parts
public import CFSG.Quasithin.Vol2.Ch5Sec1DS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Quasithin.F112R

theorem f112SliceBigL2_dsAConc_of_C (h : F112SliceBigL2 F112ConclPredC) :
    F112SliceBigL2 DSAConc := by
  have hF := listedGroupFacts
  intro G _ _ L1 L2 S hH hp
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ := h G L1 L2 S hH hp
  have hns1 := hH.vBig_iff_left.1 hp.1.1
  have hns2 := hH.vBig_iff_right.1 hp.1.2
  refine ⟨L1', L2', hsw, hZ, ?_, h2⟩
  rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact f112ListA_of hF hns1 hns2 hl
  · exact f112ListA_of hF hns2 hns1 hl

theorem dsAL2_of_partsC (hL2 : F112SliceBigL2 F112ConclPredC) (hSzL2 : IdSzL2)
    (hU3L2 : IdU3L2) (hF4 : Y9TwistedF4) (hU5 : Y9U54) : DSAL2Statement :=
  dsAL2_of_parts (f112SliceBigL2_dsAConc_of_C hL2) hSzL2 hU3L2 hF4 hU5

end CFSG.Quasithin.H13
