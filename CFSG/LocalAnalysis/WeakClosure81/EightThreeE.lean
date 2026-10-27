module

public import CFSG.CGT.T75N.PpdCyclic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModelsBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.SteinbergBQFiveCandidate

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inf_ne_bot_of_forall_mem_or_mul_mem {U N : Subgroup G} (hU : 2 < Nat.card U) {u : G}
    (hu : u ∈ U) (h : ∀ x ∈ U, x ∈ N ∨ u * x ∈ N) : U ⊓ N ≠ ⊥ := by
  intro hbot
  have hsub : (U : Set G) ⊆ {1, u⁻¹} := by
    intro x hx
    rcases h x hx with hxN | huxN
    · left
      have hmem : x ∈ U ⊓ N := ⟨hx, hxN⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    · right
      have hmem : u * x ∈ U ⊓ N := ⟨U.mul_mem hu hx, huxN⟩
      rw [hbot] at hmem
      exact eq_inv_of_mul_eq_one_right (Subgroup.mem_bot.mp hmem)
  have h1 : (U : Set G).ncard ≤ ({1, u⁻¹} : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, u⁻¹} : Set G).ncard ≤ 2 := by
    calc ({1, u⁻¹} : Set G).ncard ≤ ({u⁻¹} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : Nat.card U = (U : Set G).ncard := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  omega

end CFSG.LocalAnalysis.WeakClosure81
