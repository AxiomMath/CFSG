module

public import CFSG.StronglyEmbedded.SteinbergBUConjugateAction
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.StronglyEmbedded

open Subgroup CFSG.StronglyEmbedded.SteinbergBU

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {X Y : Subgroup G} {x : G} (hX : x ∈ normalizer (X : Set G))
    (hY : x ∈ normalizer (Y : Set G)) : x ∈ normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [← conjugate_eq_self_iff] at hX hY ⊢
  simp only [CFSG.conjugate] at hX hY ⊢
  rw [Subgroup.map_sup, hX, hY]

end CFSG.StronglyEmbedded
