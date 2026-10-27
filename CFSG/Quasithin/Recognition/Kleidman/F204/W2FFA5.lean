module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.Kleidman.F204

open Equiv

theorem alt5_no_order_four :
    ∀ g : alternatingGroup (Fin 5), g ^ 4 = 1 → g ^ 2 = 1 := by
  decide +kernel

theorem alt5_invol_centralizer_card :
    ∀ x : alternatingGroup (Fin 5), x ^ 2 = 1 → x ≠ 1 →
      (Finset.univ.filter fun g : alternatingGroup (Fin 5) => g * x = x * g).card = 4 := by
  decide +kernel

end CFSG.Quasithin.Kleidman.F204

end
