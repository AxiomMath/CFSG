module

public import CFSG.Timmesfeld.Transvection.Defs
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

theorem card_galoisField_two_mul {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]

@[expose] def unitaryLongRoot (m : ℕ) (hm : 2 ≤ m) : Fin (m / 2) → ℤ :=
  (if m % 2 = 0 then 1 else 2) • Pi.single (⟨m / 2 - 1, by omega⟩ : Fin (m / 2)) 1

@[expose] def TransvectionConclusion (H : Type) [Group H] (Δ : Set (Subgroup H)) (f : ℕ)
    (hf : 1 ≤ f) : Prop :=
  (∃ n : ℕ, ∃ hn : 2 ≤ n, ∃ Φ : ↥(StatedSp n (GaloisField 2 f)) →* H,
      Function.Bijective Φ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
        ∃ g, X = (conjSub ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
          (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ) ∨
    (∃ m : ℕ, ∃ hm : 4 ≤ m,
      ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* H,
        Function.Surjective Φ ∧ Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
          ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) m).rootGroup
            (unitaryLongRoot m (by omega))) g).map Φ)

@[expose] def TransvectionStatement : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ →
    ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧ TransvectionConclusion H Δ f hf

end CFSG.Timmesfeld.Transvection
