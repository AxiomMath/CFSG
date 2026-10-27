module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCompCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcCaseV
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloorsE
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloorsE6

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

@[expose] def RCKExcFloorsTwNine
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L → p = 3 → 9 ∣ 2 ^ f + 1 →
      3 ^ 5 ≤ Nat.card A

@[expose] def RCKExcFloorsTwOut
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L →
    ∀ (θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL)
      (A' : Subgroup (ModGL (langTag .twistedE6) GGL)),
      RCKBridgeFrame .twistedE6 f p G₀ A θ A' → p = 3 → Odd f →
        ¬ A' ≤ ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ → 3 ^ 5 ≤ Nat.card A

theorem rck_exc_floors_of_tw
    (hNine : RCKExcFloorsTwNine) (hOut : RCKExcFloorsTwOut) : RCKExcFloors := by
  unfold RCKExcFloors
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hexc hcfg θ A' hfr
  have hcard : Nat.card A' = Nat.card A := hfr.2.2.2.2.1
  rcases hexc with rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro (h | h) <;> cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
  · refine ⟨fun hp3 => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro (h | h) <;> cases h
    · intro _ hfe
      rw [hcard]
      exact rckExc_E6_floor hcfg hp3 hfe
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
  · refine ⟨fun hp3 => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro _
      rw [hcard]
      exact rckExc_E7_floor hcfg hp3
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
  · refine ⟨fun hp3 => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro _
      rw [hcard]
      have h7 := rckExc_E8_floor hcfg (Or.inl hp3)
      rw [hp3] at h7
      exact h7
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · intro _ hp5 hord
      rw [hcard]
      have h7 := rckExc_E8_floor hcfg (Or.inr ⟨hp5, hord⟩)
      rw [hp5] at h7
      exact h7
  · refine ⟨fun hp3 => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rintro (h | h) <;> cases h
    · intro h; cases h
    · intro _ h9
      rw [hcard]
      exact hNine X n f ψ p G₀ A B₁ D J L (rckCompCore_of_rpConfig hcfg) hp3 h9
    · intro _ hodd hnR
      rw [hcard]
      exact hOut X n f ψ p G₀ A B₁ D J L (rckCompCore_of_rpConfig hcfg) θ A' hfr hp3 hodd hnR
    · intro h; cases h

end CFSG.StandardType.RCKRP
