module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

structure D4qLocalData (L1 L2 S : Subgroup G) (f : ℕ) : Prop where
  card_S : Nat.card S = 2 ^ (12 * f)
  special_left : IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 L1)
  center_left : centerOf (pCoreOf 2 L1) = centerOf L1
  irred_left : ∀ W : Subgroup G, centerOf (pCoreOf 2 L1) ≤ W → W ≤ pCoreOf 2 L1 →
    L1 ≤ Subgroup.normalizer (W : Set G) → W = centerOf (pCoreOf 2 L1) ∨ W = pCoreOf 2 L1
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ (11 * f)
  nat_right : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ f ∧
    ∃ α : ↥L2 →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 L2 ∧
      IsNatSecOf L2 (centerOf (pCoreOf 2 L2)) ⊥ α
  mid_right : ∃ W : Subgroup G, centerOf (pCoreOf 2 L2) ≤ W ∧ W ≤ pCoreOf 2 L2 ∧
    Nat.card W = 2 ^ (5 * f) ∧ ⁅W, L2⁆ ≤ centerOf (pCoreOf 2 L2)

theorem D4qLocalData.card_left {L1 L2 S : Subgroup G} {f : ℕ} (h : D4qLocalData L1 L2 S f) :
    Nat.card (pCoreOf 2 L1) = 2 ^ (9 * f) := by
  rw [h.special_left.2.1, ← pow_mul]
  ring_nf

end CFSG.Quasithin.F112R.St84

end
