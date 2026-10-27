module

public import CFSG.Quasithin.Recognition.St84.TransferVertex
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

structure G24EdgeData (Ea Eb K T : Subgroup H) : Prop where
  special_left : IsSpecialPow 2 (2 ^ 2) 2 ↥(pCoreOf 2 Ea)
  center_left : centerOf (pCoreOf 2 Ea) = centerOf (oTwoPrime Ea)
  indec_left : ⁅pCoreOf 2 Ea, oTwoPrime Ea⁆ = pCoreOf 2 Ea
  irr_left : ∀ Y : Subgroup H, centerOf (pCoreOf 2 Ea) ≤ Y → Y ≤ pCoreOf 2 Ea →
    Ea ≤ Subgroup.normalizer (Y : Set H) → Y = centerOf (pCoreOf 2 Ea) ∨ Y = pCoreOf 2 Ea
  orth_left : ∃ E : Subgroup H, centerOf (pCoreOf 2 Ea) ≤ E ∧ E ≤ pCoreOf 2 Ea ∧
    (centerOf (pCoreOf 2 Ea)).relIndex E = 16 ∧ oTwoPrime Ea ≤ Subgroup.normalizer (E : Set H) ∧
    (∃ l ∈ oTwoPrime Ea, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (pCoreOf 2 Ea)) ∧
    ¬ NatSec (oTwoPrime Ea) (centerOf (pCoreOf 2 Ea)) E
  relCent_S : relCent (pCoreOf 2 Ea) (centerOf (pCoreOf 2 Ea)) T = centerOf (pCoreOf 2 Eb)
  card_right : Nat.card ↥(pCoreOf 2 Eb) = 2 ^ 10
  special_right : IsSpecialPGroup 2 ↥(pCoreOf 2 Eb)
  card_center_right : Nat.card ↥(centerOf (pCoreOf 2 Eb)) = 2 ^ 4
  natZ_right : NatSec (oTwoPrime Eb) ⊥ (centerOf (pCoreOf 2 Eb))
  mid_right : ∃ W : Subgroup H, centerOf (pCoreOf 2 Eb) ≤ W ∧ W ≤ pCoreOf 2 Eb ∧
    Nat.card ↥W = 2 ^ 6 ∧ ⁅W, oTwoPrime Eb⁆ ≤ centerOf (pCoreOf 2 Eb) ∧
    NatSec (oTwoPrime Eb) W (pCoreOf 2 Eb)
  comm_right : ⁅pCoreOf 2 Eb, oTwoPrime Eb⁆ = pCoreOf 2 Eb
  cent_right : ∀ k ∈ oTwoPrime Eb, orderOf k = 3 →
    pCoreOf 2 Eb ⊓ Subgroup.centralizer ({k} : Set H) ≤ pCoreOf 2 Ea
  card_T : Nat.card ↥T = 2 ^ 12
  card_K : Nat.card ↥K = 2 ^ 12 * 3 ^ 2
  card_inf : Nat.card ↥(pCoreOf 2 Ea ⊓ pCoreOf 2 Eb) = 2 ^ 8

abbrev G24TransferData (L1 L2 S : Subgroup H) : Prop :=
  G24EdgeData (f112saP1' L1 L2 S) (f112saP2' L1 L2 S) (f112saK L1 L2 S) (S ⊓ f112saK L1 L2 S)

theorem g24TransferData_swap_iff (L1 L2 S : Subgroup H) :
    G24TransferData L2 L1 S ↔
      G24EdgeData (f112saP2' L1 L2 S) (f112saP1' L1 L2 S) (f112saK L1 L2 S)
        (S ⊓ f112saK L1 L2 S) := by
  rw [G24TransferData, f112saP1'_eq_P2'_swap L2 L1 S, f112saP2'_eq_P1'_swap L2 L1 S,
    f112saK_comm]

theorem G24EdgeData.card_pCoreOf_left {Ea Eb K T : Subgroup H}
    (h : G24EdgeData Ea Eb K T) : Nat.card ↥(pCoreOf 2 Ea) = 2 ^ 10 := by
  have h := h.special_left.2.1
  norm_num at h ⊢
  exact h

theorem G24EdgeData.card_centerOf_left {Ea Eb K T : Subgroup H}
    (h : G24EdgeData Ea Eb K T) : Nat.card ↥(centerOf (pCoreOf 2 Ea)) = 2 ^ 2 := by
  rw [CFSG.Quasithin.A1c.centerOf_eq_map_center,
    Subgroup.card_map_of_injective (pCoreOf 2 Ea).subtype_injective]
  exact h.special_left.2.2

end CFSG.Quasithin.F112R.St84
