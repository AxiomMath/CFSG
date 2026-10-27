module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveDesignDivisibility

open scoped BigOperators

theorem five_dvd_lambda
    {X : Type*} [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 31)
    (B : Finset (Finset X)) (hB : ∀ b ∈ B, b.card = 7)
    (lam : ℕ) (hlam : ∀ s : Finset X, s.card = 5 → (B.filter (s ⊆ ·)).card = lam) :
    5 ∣ lam := by
  classical
  obtain ⟨a,ha,hac⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset X)) (n := 2) (by simp [hcard])
  let S := ((Finset.univ : Finset X).powersetCard 5).filter (a ⊆ ·)
  let T := B.filter (a ⊆ ·)
  have hSc : S.card = 3654 := by
    rw [Finset.card_filter_powersetCard_subset _ _ _ ha (by omega),Finset.card_univ,hcard,hac]
    decide
  have habove (s : Finset X) (hs : s ∈ S) :
      (Finset.bipartiteAbove (fun s b : Finset X => s ⊆ b) T s).card = lam := by
    have has : a ⊆ s := (Finset.mem_filter.mp hs).2
    have hsc : s.card = 5 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
    have he : Finset.bipartiteAbove (fun s b : Finset X => s ⊆ b) T s = B.filter (s ⊆ ·) := by
      ext b
      simp only [Finset.mem_bipartiteAbove,Finset.mem_filter,T]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,has.trans h.2⟩,h.2⟩
    rw [he,hlam s hsc]
  have hbelow (b : Finset X) (hb : b ∈ T) :
      (Finset.bipartiteBelow (fun s b : Finset X => s ⊆ b) S b).card = 10 := by
    obtain ⟨hbB,hab⟩ := Finset.mem_filter.mp hb
    have he : Finset.bipartiteBelow (fun s b : Finset X => s ⊆ b) S b =
        (b.powersetCard 5).filter (a ⊆ ·) := by
      ext s
      simp only [Finset.mem_bipartiteBelow,Finset.mem_filter,Finset.mem_powersetCard,
        Finset.subset_univ,true_and,S]
      tauto
    rw [he,Finset.card_filter_powersetCard_subset _ _ _ hab (by omega),hB b hbB,hac]
    decide
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := T) (fun s b : Finset X => s ⊆ b)
  rw [Finset.sum_congr rfl habove,Finset.sum_congr rfl hbelow] at he
  simp only [Finset.sum_const,nsmul_eq_mul,hSc] at he
  omega

end FiveTransitive.Degree31FiveDesignDivisibility

end CFSG
