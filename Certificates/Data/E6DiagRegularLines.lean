module

public import Certificates.Data.E6DiagRegular

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def killIdx (T : RootTables) (nr : ℕ) (kvec : List ℕ) : List ℕ :=
  (List.range nr).filter fun j => pairZ T j (castL kvec) % 3 == 0

@[expose] def sumRootL (T : RootTables) (nr : ℕ) (a b : ℕ) : Bool :=
  (List.range nr).any fun c =>
    T.vecs.getD c [] == List.zipWith (· + ·) (T.vecs.getD a []) (T.vecs.getD b [])

@[expose] def fixesIdxL (C : RootCertificate .E6) (t : List ℕ) (a : ℕ) : Bool :=
  List.ofFn (C.tupleVec t (C.root a)) == List.ofFn (C.root a)

@[expose] def a2FixedL (C : RootCertificate .E6) (T : RootTables) (kill : List ℕ) (t : List ℕ) :
    Bool :=
  let fx := kill.filter (fixesIdxL C t)
  fx.any fun a => fx.any fun b => sumRootL T C.roots.length a b

@[expose] def combVec (c₁ c₂ : ℕ) (v₁ v₂ : List ℕ) : List ℕ :=
  (List.range Tag.E6.rank).map fun i => (c₁ * v₁.getD i 0 + c₂ * v₂.getD i 0) % 3

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular
