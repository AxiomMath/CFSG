module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5ReflMat
public import Certificates.Certificate709601
public import Certificates.Certificate709602

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem t5ReflFix_holds : T5ReflFix :=
  Certificates.certificate709601

theorem t5ReflAll_holds : T5ReflAll :=
  Certificates.certificate709602

theorem t5ThmA_holds :
    T5ThmA :=
  t5ThmA_of_refl t5ReflFix_holds t5ReflAll_holds

end CFSG.StandardType.FrameRoute.FS81

end
