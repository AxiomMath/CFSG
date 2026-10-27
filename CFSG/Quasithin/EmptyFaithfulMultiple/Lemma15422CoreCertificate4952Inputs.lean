module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Cases

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L15422

@[expose] def cycThree : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def cycFive : Equiv.Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5

end CFSG.Quasithin.EmptyFaithfulMultiple.L15422
