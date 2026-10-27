module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsStep

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] {n : ℕ}

theorem clsSets_eq_map_cls (μ : Multiset (Coord n)) :
    clsSets μ =
      Multiset.map (fun s : Finset (Coord n) => (s : Set (Coord n))) (μ.map cls) := by
  rw [clsSets, Multiset.map_map]
  rfl

theorem map_cls_eq_of_clsSets_eq {μ μ' : Multiset (Coord n)} (h : clsSets μ = clsSets μ') :
    μ.map cls = μ'.map cls := by
  have h' : Multiset.map (fun s : Finset (Coord n) => (s : Set (Coord n))) (μ.map cls) =
      Multiset.map (fun s : Finset (Coord n) => (s : Set (Coord n))) (μ'.map cls) := by
    simpa only [clsSets_eq_map_cls] using h
  exact Multiset.map_injective (f := fun s : Finset (Coord n) => (s : Set (Coord n)))
    (fun a b hab => Finset.coe_inj.mp hab) h'

namespace Conf

variable [Finite G] (c : Conf G n)

theorem pass : ∀ i j : ℤ, i ≤ j → j ≤ i + c.pattern.J → c.pattern.Pass c.k₀ c.m₀ i j := by
  intro i j hij hj
  obtain ⟨lR, hR, hRfac⟩ := c.exists_ySeries_chainR hij hj
  obtain ⟨lL, hL, hLfac⟩ := c.exists_ySeries_chainL hij hj
  have hJH := facMultiset_eq (Y := c.H) (chiLab c.ζ c.d₁ c.d₂)
    (fun S S' D h h' hne => chiLab_eq_inf c.d₁_mem_H c.d₂_mem_H h h' hne)
    (Nat.card (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j)) (win c.Q₁ c.Q₂ c.x₁ c.x₂ 0 c.pattern.J)
    (win c.Q₁ c.Q₂ c.x₁ c.x₂ i j) rfl lR lL hR hL
  refine map_cls_eq_of_clsSets_eq ?_
  rw [← hRfac, ← hLfac, hJH]

end Conf

end CFSG.Quasithin.Stroth.G5

end
