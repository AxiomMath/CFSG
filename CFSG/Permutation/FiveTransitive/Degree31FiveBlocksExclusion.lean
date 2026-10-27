module

public import CFSG.Permutation.FiveTransitive.Degree31BlockPairs
public import CFSG.Permutation.FiveTransitive.Degree31FivePairsExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveBlocksExclusion

open MulAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (hH : Nat.card (fixingSubgroup P s) = 4096)
    (b : Fin 5 → Set X) (hinj : Function.Injective b)
    (hb : ∀ i, (b i).ncard = 7) (hsb : ∀ i, s ⊆ b i)
    (hK : ∀ i, Nat.card (fixingSubgroup P (b i)) = 2048) : False := by
  have hd (i : Fin 5) := Degree31BlockPairs.block_data
    P hcard h5 hnotAlt s hs hH (b i) (hb i) (hsb i) (hK i)
  apply Degree31FivePairsExclusion.excluded P hcard h5 hnotAlt
    (fixingSubgroup P s) hH s hs le_rfl (fun i => b i \ s)
    (fun i => (hd i).1) ?_ (fun i => (hd i).2.1)
    (fun h i x hx => (hd i).2.2 h x hx)
  intro i j hij
  exact Degree31BlockPairs.disjoint_pairs P hcard h5 hnotAlt s hs hH
    (b i) (b j) (hb i) (hb j) (hsb i) (hsb j) (hK i) (hK j)
    (fun he => hij (hinj he))

end FiveTransitive.Degree31FiveBlocksExclusion

end CFSG
