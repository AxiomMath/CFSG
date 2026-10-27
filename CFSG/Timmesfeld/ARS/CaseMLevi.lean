module

public import CFSG.Timmesfeld.ARS.Sec12Basic

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace CaseM

theorem card_galoisField_two_mul {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]

end CaseM

@[expose] def CaseMLeviInput₇ : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G), Sec12 R A A₀ →
    LeviConnected R A A₀ → ∀ (f : ℕ) (hf : 1 ≤ f), Nat.card A = 2 ^ f →
      (∃ Φ : ↥(StatedSp 3 (GaloisField 2 f)) →* G, Function.Injective Φ ∧
        Φ.range = levi R A A₀ ∧ ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
          ∃ g, X = (conjSub ((Symplectic.rootDatum 3 (GaloisField 2 f)).rootGroup
            (Pi.single (2 : Fin 3) 1)) g).map Φ) ∨
      (∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G,
        Φ.ker ≤ Subgroup.center _ ∧ Φ.range = levi R A A₀ ∧ ∀ X : Subgroup G,
          X ∈ leviSet R A A₀ ↔
            ∃ g, X = (conjSub ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
              (Pi.single (2 : Fin 3) 1)) g).map Φ) ∨
      (∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 7) →* G,
        Φ.ker ≤ Subgroup.center _ ∧ Φ.range = levi R A A₀ ∧ ∀ X : Subgroup G,
          X ∈ leviSet R A A₀ ↔
            ∃ g, X = (conjSub ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 7).rootGroup
              (2 • Pi.single (2 : Fin 3) 1)) g).map Φ)

@[expose] def CaseMLeviInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G), Sec12 R A A₀ →
    LeviConnected R A A₀ → ∀ (f : ℕ) (hf : 1 ≤ f), Nat.card A = 2 ^ f →
      (∃ Φ : ↥(StatedSp 3 (GaloisField 2 f)) →* G, Function.Injective Φ ∧
        Φ.range = levi R A A₀ ∧ ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
          ∃ g, X = (conjSub ((Symplectic.rootDatum 3 (GaloisField 2 f)).rootGroup
            (Pi.single (2 : Fin 3) 1)) g).map Φ) ∨
      (∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G,
        Φ.ker ≤ Subgroup.center _ ∧ Φ.range = levi R A A₀ ∧ ∀ X : Subgroup G,
          X ∈ leviSet R A A₀ ↔
            ∃ g, X = (conjSub ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
              (Pi.single (2 : Fin 3) 1)) g).map Φ)

end CFSG.Timmesfeld.ARS
