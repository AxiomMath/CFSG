module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbEven3
public import CFSG.Quasithin.Recognition.Stroth.Str86AbOddModule

import CFSG.Quasithin.Recognition.Stroth.Str86AbM6
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5Main
import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleHolds
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2

public section

namespace CFSG.Quasithin.Stroth

theorem str86UnitaryM6_holds :
    Str86UnitaryM6 := by
  intro G _ _ L1 L2 S k m F _ _ hI hZQ t htP htQ ht2
  exact str86_sq_le_relIndex_conjClosure_of_mem_p1 hI hZQ htP htQ ht2

theorem str86CritNot3_of_lemmaW
    (hW : Str86LemmaW) :
    Str86CritNot3 :=
  str86CritNot3_of str86UnitaryM6_holds hW str86OddModuleOf_holds

theorem str86ZNotLeAb_of_inputs
    (hE1 : Str86E1)
    (hW : Str86LemmaW) (h5 : Str86CritNotOdd5) : Str86ZNotLeAb :=
  str86ZNotLeAb_of_crit (str86CritNotEven_of hE1 hW) (str86CritNot3_of_lemmaW hW) h5

theorem str86ZNotLe_of_inputs
    (hE1 : Str86E1)
    (hW : Str86LemmaW) (h5 : Str86CritNotOdd5) : Str86ZNotLe :=
  str86ZNotLe_of_parts (str86ZNotLeAb_of_inputs hE1 hW h5) str86ZNotLeNonab_holds

theorem str86CritNotOdd5_of_lemmaW
    (hW : Str86LemmaW) :
    Str86CritNotOdd5 :=
  str86CritNotOdd5_of (str86OddRGeQSq_of str86UnitaryM6_holds hW) str86OddModuleOf_holds

theorem str86ZNotLe_of_e1_lemmaW
    (hE1 : Str86E1)
    (hW : Str86LemmaW) : Str86ZNotLe :=
  str86ZNotLe_of_inputs hE1 hW (str86CritNotOdd5_of_lemmaW hW)

end CFSG.Quasithin.Stroth

end
