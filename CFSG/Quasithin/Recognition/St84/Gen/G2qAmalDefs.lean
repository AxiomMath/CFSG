module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

structure G2qLocalData (L1 L2 S : Subgroup G) (f : ℕ) : Prop where
  card_S : Nat.card S = 2 ^ (6 * f)
  special_left : IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L1)
  center_left : centerOf (pCoreOf 2 L1) = centerOf L1
  special_right : IsSpecialPGroup 2 ↥(pCoreOf 2 L2)
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ (5 * f)
  nat_right : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ f ∧
    ∃ α : ↥L2 →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 L2 ∧
      IsNatSecOf L2 (centerOf (pCoreOf 2 L2)) ⊥ α ∧
      ∃ W : Subgroup G, centerOf (pCoreOf 2 L2) ≤ W ∧ W ≤ pCoreOf 2 L2 ∧
        Nat.card W = 2 ^ (3 * f) ∧ ⁅W, L2⁆ ≤ centerOf (pCoreOf 2 L2) ∧
        IsNatSecOf L2 (pCoreOf 2 L2) W α
  card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ (4 * f)

theorem G2qLocalData.card_left {L1 L2 S : Subgroup G} {f : ℕ} (h : G2qLocalData L1 L2 S f) :
    Nat.card (pCoreOf 2 L1) = 2 ^ (5 * f) := by
  rw [h.special_left.2.1, ← pow_mul]
  ring_nf

end CFSG.Quasithin.F112R.St84

end
