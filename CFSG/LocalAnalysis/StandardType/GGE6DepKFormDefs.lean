module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

@[expose] def gS (i : Fin 5) : Mat6 := gensL i.castSucc

@[expose] def gbeta (c : ZMod 3) : Mat6 :=
  !![1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, c * c, -c; 0, 0, 0, 0, -c, 1]

@[expose] def bilK (c : ZMod 3) (u v : Vec6) : ZMod 3 := u ⬝ᵥ (gbeta c).mulVec v

@[expose] def normK (c : ZMod 3) (v : Vec6) : ZMod 3 := bilK c v v

@[expose] def rK (c : ZMod 3) (h : Vec6) : Mat6 := 1 + Matrix.vecMulVec h ((gbeta c).mulVec h)

@[expose] def kY (c : ZMod 3) : Vec6 := ![0, 0, 0, 0, 1, c]

@[expose] def kNorm1 (c : ZMod 3) : Finset Vec6 := Finset.univ.filter fun v => normK c v = 1

@[expose] def cS : Finset Vec6 :=
  Finset.univ.filter fun v => v 4 = 0 ∧ v 5 = 0 ∧ norm6 v = 1

@[expose] def mpart (h : Vec6) : Vec6 := ![h 0, h 1, h 2, h 3, 0, 0]

@[expose] def fpart (c : ZMod 3) (h : Vec6) : ZMod 3 := c * h 4 - h 5

@[expose] def KGen (c : ZMod 3) (h : Vec6) : Prop :=
  ∀ X : Finset Vec6, X ⊆ kNorm1 c → (∀ u ∈ X, ∀ w ∈ X, w + bilK c w u • u ∈ X) →
    (∀ u ∈ X, u + kY c ∈ X) → cS ⊆ X → h ∈ X → X = kNorm1 c

end E6Dep

end CFSG.StandardType

end
