module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.KGLangS1EExc
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcE6
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcTwE6
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcE6Even
import CFSG.LocalAnalysis.StandardType.KGLangS1EExcTwE6Odd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgLangAxisS1ExcInput_holds :
    KGLangAxisS1ExcInput := by
  intro p lab hp hp2 hlab hE
  obtain ⟨htag, hp3, h3⟩ := hE
  subst hp3
  rcases htag with h | h | h
  · rcases Nat.even_or_odd lab.n with he | ho
    · exact kgLangS1E_cont_E6_even hlab h h3 he
    · exact kgLangS1E_cont_E6_odd hlab h h3 ho
  · rcases Nat.even_or_odd lab.n with he | ho
    · exact kgLangS1E_cont_twE6_even hlab h h3 he
    · exact kgLangS1E_cont_twE6_odd hlab h h3 ho
  · exact kgLangS1E_cont_E7 hlab h h3

end CFSG.StandardType
