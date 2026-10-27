module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section ThreeC


@[expose] def GGF4TwoThreeCSolv (K : Type) [Field K] [CharP K 2] : Prop :=
  Group.IsSolvable (Subgroup.centralizer
    ({TableBF4Two.torus3 K (fun _ => Multiplicative.ofAdd (1 : ZMod 3))} :
      Set (adjointGroup .F4 K)))

@[expose] def GGF4TwoThreeCSolvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGF4TwoThreeCSolv K

end ThreeC

end CFSG.StandardType.SmallExc

end
