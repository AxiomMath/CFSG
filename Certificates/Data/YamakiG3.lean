module

public import Certificates.Data.YamakiPres

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open Matrix

@[expose] def bicomLetters : List (Fin 12) := [3, 1, 4, 5, 6, 2, 7]

@[expose] def bicomGen (k : Fin 2) : Fin 3 ⊕ Fin 3 → ZMod 2 := vecOf (![1, 16] k)

@[expose] def bicomTerms : Fin 6 → List (Fin 2 × List (Fin 12)) :=
  ![[(0, [])], [(0, [6]), (0, [2])], [(0, []), (1, []), (0, [6])], [(0, [7])], [(1, [])],
    [(1, [1])]]

@[expose] def bicomWordVec (w : List (Fin 12)) (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    Fin 3 ⊕ Fin 3 → ZMod 2 :=
  w.foldr (fun i u => yamakiMat i *ᵥ u) v

@[expose] def bicomTermsVec (y : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2)
    (l : List (Fin 2 × List (Fin 12))) : Fin 3 ⊕ Fin 3 → ZMod 2 :=
  (l.map fun t => bicomWordVec t.2 (y t.1)).sum

@[expose] def bicomMat (y : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun r j => bicomTermsVec y (bicomTerms (finSumFinEquiv j)) r

@[expose] def BicomExpand : Prop :=
  (∀ j : Fin 6, ∀ t ∈ bicomTerms j, ∀ i ∈ t.2, i ∈ bicomLetters) ∧
    ∀ j : Fin 3 ⊕ Fin 3, bicomTermsVec bicomGen (bicomTerms (finSumFinEquiv j)) = Pi.single j 1

@[expose] def BicomCommute : Prop :=
  ∀ y₁ y₂ : Fin 3 ⊕ Fin 3 → ZMod 2,
    (∀ i ∈ bicomLetters, bicomMat ![y₁, y₂] * yamakiMat i = yamakiMat i * bicomMat ![y₁, y₂]) →
      bicomMat ![y₁, y₂] * yamakiMat 8 = yamakiMat 8 * bicomMat ![y₁, y₂]

end CFSG.ClassicalInvolution.Solomon73.Yamaki
