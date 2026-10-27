module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs

public section

namespace CFSG.StandardType.FF81.CentE6

open CFSG CFSG.Open

structure E6Frame (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (n : ℕ) (b : G)
    (L : Subgroup G) (K : ℕ → Subgroup G) (t : G) : Prop where
  nonab : ∃ x y : G, x * y ≠ y * x
  charTwo : IsCharTwoType G
  hypA : HypA G n b L
  upstream : Upstream n b L K t
  yData : YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t
  five : n = 5
  label : GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ))

end CFSG.StandardType.FF81.CentE6
