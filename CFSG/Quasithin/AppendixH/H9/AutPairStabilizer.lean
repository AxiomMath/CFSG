module

public import CFSG.Quasithin.AppendixH.H9.AutPair.ConjugationAction

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem nonempty_mulEquiv_aut_pairStab (m : ℕ) (hm : 3 ≤ m) :
    Nonempty (↥(Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0 * pairVec 0 (ez m)))) ≃*
      MulAut (GL (Fin m) (ZMod 2))) :=
  ⟨AutPair.mulEquivAut hm⟩

end CFSG.ASVolI.ChH
