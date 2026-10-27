module

public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HN.F5Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5

@[expose] def basePt (k : ℕ) : Fin hnsData.n :=
  ⟨Data.baseList.getD k 0 % hnsData.n, Nat.mod_lt _ (by decide)⟩

@[expose] def chainPos : List ℕ := [0, 2, 19, 1]

@[expose] def chainPt (i : ℕ) : Fin hnsData.n := basePt (chainPos.getD i 0)

@[expose] def chainSizes : List ℕ := [10395, 720, 32]

@[expose] def LevelFacts : Prop :=
  ∀ l < 3, ∃ f : Fin (chainSizes.getD l 0) → J hnsData,
    (∀ k, ∀ i ≤ l, f k • chainPt i = chainPt i) ∧ Function.Injective fun k => f k • chainPt (l + 1)

end CFSG.Sporadic.HNSchreier.Native

end
