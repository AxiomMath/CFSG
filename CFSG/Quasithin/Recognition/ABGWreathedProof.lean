module

public import CFSG.Quasithin.Recognition.U33Defs
public import CFSG.Milestones.LR_wreathed_simple_recognition

public section

namespace CFSG.Quasithin

theorem abgWreathedRecognition
    : ABGWreathedRecognition :=
  fun G _ _ _ hnonab P hwr => CFSG.Milestones.lr_wreathed_simple_recognition_2 G hnonab P hwr

end CFSG.Quasithin
