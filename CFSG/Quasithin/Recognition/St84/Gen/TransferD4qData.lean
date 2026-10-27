module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open

abbrev D4qEdgeData {H : Type} [Group H] [Finite H] (L1 L2 S : Subgroup H) (f : ℕ) : Prop :=
  D4qLocalData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
    (S ⊓ f112saK L1 L2 S) f

end CFSG.Quasithin.F112R.St84

end
