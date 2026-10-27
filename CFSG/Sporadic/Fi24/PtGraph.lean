module

public import CFSG.Sporadic.Fi24.OrbitBase

public section

namespace CFSG.Sporadic.Fi24

noncomputable abbrev seedGrp : Subgroup (GL (Fin 781) (ZMod 3)) :=
  Subgroup.closure {g | g.val = mA ∨ g.val = mB}

noncomputable abbrev subImg (g : GL (Fin 781) (ZMod 3))
    (V : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  V.map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3)))

@[expose] def IsPt (V : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : Prop :=
  ∃ g ∈ seedGrp, subImg g (pt 0).sp = V

@[expose] def PtAdj (V W : Submodule (ZMod 3) (Fin 781 → ZMod 3)) : Prop :=
  ∃ g ∈ seedGrp, subImg g (pt 0).sp = V ∧
    subImg g ((pt 0).sp.map (Matrix.mulVecLin mA)) = W

@[expose] def ptFix (g : GL (Fin 781) (ZMod 3)) : Set (Submodule (ZMod 3) (Fin 781 → ZMod 3)) :=
  {V | IsPt V ∧ subImg g V = V}

end CFSG.Sporadic.Fi24

end
