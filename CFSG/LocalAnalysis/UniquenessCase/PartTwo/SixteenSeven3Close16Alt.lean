module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Mbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem close16_le_stabTil (hS : Close16Setting D V L hV) : D.M ≤ stabTil ⊥ V :=
  le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
    hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀

theorem close16_lbar_isAlt (hS : Close16Setting D V L hV) : IsAlt ↥(lBar ⊥ V hV L) 8 := by
  obtain ⟨-, ⟨L₀, -, -, hLnL, -⟩, -⟩ := hS.shape
  exact CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hLnL

theorem close16_lbar_not_commutative (hS : Close16Setting D V L hV) :
    ¬ IsMulCommutative ↥(lBar ⊥ V hV L) := by
  intro hc
  haveI : IsSimpleGroup ↥(lBar ⊥ V hV L) := close16_lbar_simple hS
  haveI : IsMulCommutative ↥(lBar ⊥ V hV L) := hc
  have hp : (Nat.card ↥(lBar ⊥ V hV L)).Prime := (Group.is_simple_iff_prime_card).mp inferInstance
  rw [close16_card_lbar hS] at hp
  exact (by norm_num : ¬ Nat.Prime 20160) hp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
