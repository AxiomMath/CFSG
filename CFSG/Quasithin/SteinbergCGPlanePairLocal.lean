module

public import CFSG.Quasithin.SteinbergCGPlanePairTransport

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SteinbergCG

open Subgroup CFSG CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.QuasithinUnique.Setup.Wreath

theorem iSupIndep_fin_two {α : Type*} [CompleteLattice α] {f : Fin 2 → α}
    (h : Disjoint (f 0) (f 1)) : iSupIndep f :=
  (iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)).mpr h

end CFSG.Quasithin.SteinbergCG
