module

public import CFSG.Sporadic.Fi24.Octads

public section

namespace CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] rAction

structure Fi24EFacts : Prop where
  cent : ∀ h : R, (∀ i, h * bbar i = bbar i * h) → h ∈ Subgroup.closure (Set.range bbar)
  card : Nat.card (Subgroup.closure (Set.range bbar)) = 4096
  fixPairs : ∀ q : Fin 306936, (∀ i, (bbar 0 * bbar i) • q = q) → ∃ k, bbarPt k = q
  fixZ : Nat.card {k : Fin 306936 // (bbar 0 * bbar 3 * bbar 13 * bbar 15) • k = k} = 504

end CFSG.Sporadic.Fi24
