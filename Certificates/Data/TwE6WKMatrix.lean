module

public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] noncomputable def wkMatrix (w : WeylGroup TwistTag.E6.tag) :
    Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
  fun i k => (if i = k then 1 else 0) +
    (w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) (TwistTag.E6.perm k)

end CFSG.StandardType.TwE6RootKill
