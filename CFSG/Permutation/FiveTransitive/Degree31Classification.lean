module

public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerOrder
public import CFSG.Permutation.FiveTransitive.Degree31BlocksUniform
public import CFSG.Permutation.FiveTransitive.Degree31BlockExists
public import CFSG.Permutation.FiveTransitive.Degree31FiveDesignDivisibility
public import CFSG.Permutation.FiveTransitive.Degree31FiveBlocksExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree31Classification

open MulAction Degree31Blocks

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  have hall := Degree31FiveFixerOrder.five_fixer_card P hcard h5 hnotAlt
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset X)) (n := 5) (by simp [hcard])
  have hs' : (s : Set X).ncard = 5 := by simpa using hs
  let T := (blockFinset P).filter (s ⊆ ·)
  have hdiv : 5 ∣ T.card := by
    apply Degree31FiveDesignDivisibility.five_dvd_lambda hcard (blockFinset P)
      (fun b hb => ((mem_blockFinset P b).mp hb).1) T.card
    intro t ht
    exact card_filter_eq_of_five P h5 t s ht hs
  obtain ⟨b,hb,hsb,hKb⟩ := Degree31BlockExists.exists_block
    P hcard h5 hnotAlt hall (s : Set X) hs'
  have hmem : b.toFinite.toFinset ∈ T := by
    apply Finset.mem_filter.mpr
    constructor
    · rw [mem_blockFinset]
      change b.toFinite.toFinset.card = 7 ∧
        Nat.card (fixingSubgroup P (b.toFinite.toFinset : Set X)) = 2048
      simpa only [← Set.ncard_eq_toFinset_card,Set.Finite.coe_toFinset] using And.intro hb hKb
    · intro x hx
      exact (Set.Finite.mem_toFinset b.toFinite).mpr (hsb hx)
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨_,hmem⟩
  have hcount : 5 ≤ T.card := Nat.le_of_dvd hpos hdiv
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 5) ≤ Fintype.card T by simpa using hcount)
  have hemem (i : Fin 5) : (e i).val ∈ blockFinset P ∧ s ⊆ (e i).val :=
    Finset.mem_filter.mp (e i).property
  apply Degree31FiveBlocksExclusion.excluded P hcard h5 hnotAlt
    (s : Set X) hs' (hall _ hs') (fun i => ((e i).val : Set X)) ?_ ?_ ?_ ?_
  · intro i j he
    apply e.injective
    apply Subtype.ext
    exact Finset.coe_injective he
  · intro i
    have hh := ((mem_blockFinset P _).mp (hemem i).1).1
    simpa using hh
  · intro i
    exact_mod_cast (hemem i).2
  · intro i
    exact ((mem_blockFinset P _).mp (hemem i).1).2

theorem subgroup_card_classification
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) :
    Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Nat.card P = (Fintype.card X).factorial / 2) := by
  rcases FiveTransitive.alt_le_perm_card_dichotomy X P (by omega)
    (alternatingGroup_le P hcard h5) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by omega,h⟩

end FiveTransitive.Degree31Classification

end CFSG
