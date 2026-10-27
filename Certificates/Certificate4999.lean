module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSixTotalsInputs

public section

namespace CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm CFSG.QuasithinUnique

private theorem total_inj : ∀ i j : Fin 6, total i = total j → i = j := by
  decide +kernel

private theorem total_closed_gen : ∀ (a : Fin 5) (i : Fin 6),
    ∃ j : Fin 6, act (swap a.castSucc a.succ) (total i) = total j := by
  decide +kernel

end CFSG.QuasithinUnique.Ch1.AltSix

namespace Certificates

open Equiv Equiv.Perm CFSG.QuasithinUnique.Ch1.AltSix in
theorem certificate4999 : (∀ i j : Fin 6, total i = total j → i = j)
    ∧ (∀ (a : Fin 5) (i : Fin 6),
    ∃ j : Fin 6, act (swap a.castSucc a.succ) (total i) = total j) :=
  ⟨CFSG.QuasithinUnique.Ch1.AltSix.total_inj, CFSG.QuasithinUnique.Ch1.AltSix.total_closed_gen⟩

end Certificates
