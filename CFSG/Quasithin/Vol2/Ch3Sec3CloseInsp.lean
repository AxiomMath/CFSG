module

public import CFSG.Quasithin.Vol2.Ch3Sec3CloseA
public import CFSG.Quasithin.Vol2.Ch3Sec3CloseB

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem inspClose_holds
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : InspClose := by
  intro G _ _ T M L D h hTL hA6 hTC hc φ hφT
  rcases hc with ⟨hQV, hIrr⟩ | hb
  · exact CloseA.inspClose_a h h38 h39 hTL hA6 hTC hQV hIrr φ hφT
  · exact CloseB.inspClose_b h h38 h39 hTL hA6 hTC hb φ hφT

end CFSG.Quasithin.H13
