module

public import CFSG.Quasithin.EmptyFaithful.ModDData
public import CFSG.Quasithin.Recognition.CertU33DcData

public section

namespace CFSG.Quasithin.H.U33Sq

open CFSG.Quasithin CFSG.Quasithin.ModD

@[expose] def telP (j : Fin 32) : Equiv.Perm (Fin 63) :=
  evalW vImg (u33Word (u33TelWords.getD j.val ""))

theorem card_fix_sq :
    (Finset.univ.filter fun i : Fin 63 => ∀ j : Fin 32, (telP j * telP j) i = i).card = 3 := by
  decide +kernel

end CFSG.Quasithin.H.U33Sq
