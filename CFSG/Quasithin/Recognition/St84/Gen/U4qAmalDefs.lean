module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def IsTwoNatType (L : Subgroup G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ α : L →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective α ∧ α.ker = CFSG.pCore 2 L ∧
    ∃ β : blockU L →* Multiplicative (Matrix (Fin 2) (Fin 2) F),
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      ∀ ℓ : L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) =
          (α ℓ : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd (β u)

structure U4qLocalData (L1 L2 S : Subgroup G) (f : ℕ) : Prop where
  card_S : Nat.card S = 2 ^ (6 * f) ∨ Nat.card S = 2 * 2 ^ (6 * f)
  special_left : CFSG.Quasithin.IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L1)
  center_left : L1 ≤ Subgroup.centralizer (CFSG.Quasithin.centerOf (pCoreOf 2 L1) : Set G)
  twoNat_left : IsTwoNatType L1 f
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ (4 * f)
  omega_right : CFSG.Quasithin.IsOmega4MinusType L2 f
  card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ (3 * f)

theorem U4qLocalData.card_left {L1 L2 S : Subgroup G} {f : ℕ} (h : U4qLocalData L1 L2 S f) :
    Nat.card (pCoreOf 2 L1) = 2 ^ (5 * f) := by
  rw [h.special_left.2.1, ← pow_mul]
  ring_nf

end CFSG.Quasithin.F112R.St84

end
