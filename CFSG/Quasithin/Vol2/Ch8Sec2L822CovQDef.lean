module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

structure CoverQData (Q : Type) [Group Q] [Finite Q] (S P Kt B : Subgroup Q) (yt : Q) : Prop where
  S2 : IsPGroup 2 S
  Sodd : ¬ 2 ∣ S.index
  SP : S ≤ P
  KP : Kt ≤ P
  P9 : ¬ 9 ∣ Nat.card P
  Kperf : ⁅Kt, Kt⁆ = Kt
  ytK : yt ∈ Kt
  Kphi : ∃ φ : ↥Kt →* ↥(alternatingGroup (Fin 5)), Function.Surjective φ ∧ φ ⟨yt, ytK⟩ ≠ 1
  Bperf : ⁅B, B⁆ = B
  SB : S ≤ Subgroup.normalizer (B : Set Q)
  Bhat : IsHat (↥B ⧸ CFSG.pCore 2 ↥B) (alternatingGroup (Fin 6))
  ytB : yt ∈ B
  yt3 : yt ^ 3 = 1
  ytc : (QuotientGroup.mk (⟨yt, ytB⟩ : ↥B) : ↥B ⧸ CFSG.pCore 2 ↥B) ∈
    Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)

@[expose] def J4CoverFacts : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) →
    ∀ S : Subgroup Q, IsPGroup 2 S → Nat.card S = 2 ^ 21 →
      ∃ z₁ : Q, z₁ ∈ S ∧ z₁ ≠ 1 ∧ z₁ ^ 2 = 1 ∧ (∀ s ∈ S, s * z₁ = z₁ * s) ∧
        (∀ X : Subgroup Q, S ≤ X → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X →
          X ≤ Subgroup.centralizer ({z₁} : Set Q)) ∧
        (∀ B : Subgroup Q, ⁅B, B⁆ = B → S ≤ Subgroup.normalizer (B : Set Q) →
          IsHat (↥B ⧸ CFSG.pCore 2 ↥B) (alternatingGroup (Fin 6)) →
          B ≤ Subgroup.centralizer ({z₁} : Set Q)) ∧
        ∃ (R : Type) (_ : Group R) (_ : Finite R)
          (ρ : ↥(Subgroup.centralizer ({z₁} : Set Q)) →* R), Function.Surjective ρ ∧
          (∀ d ∈ ρ.ker, ∃ n : ℕ, d ^ (2 ^ n) = 1) ∧
          ∃ N₀ : Subgroup R, N₀.Normal ∧ N₀.index = 2 ∧
            IsHat ↥N₀ (CFSG.Blueprint.NativeSporadic.Carrier .M22)

end CFSG.Quasithin.H13
