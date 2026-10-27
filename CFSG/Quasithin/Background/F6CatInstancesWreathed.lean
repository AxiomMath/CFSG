module

public import CFSG.Quasithin.Background.F6CatRecogInputs2
public import CFSG.Milestones.LR_wreathed_simple_recognition

public section

namespace CFSG.Quasithin

namespace F6

theorem wreathedRecognitionStatement
    : WreathedRecognitionStatement :=
  fun G _ _ _ hnonab hwr => CFSG.Milestones.lr_wreathed_simple_recognition_1 G hnonab hwr

end F6

end CFSG.Quasithin
