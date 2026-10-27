module

public import CFSG.Timmesfeld.ARS.CaseOADegSp
public import CFSG.Timmesfeld.ARS.CaseOADegThree

public section

namespace CFSG.Timmesfeld.ARS

open Transvection CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

namespace CaseOADeg

@[expose] def OADegSUInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ₁ Δ₂ : Set (Subgroup G)),
    DegOA R A A₀ Δ₁ Δ₂ → ∀ (f : ℕ) (hf : 1 ≤ f), (∀ X ∈ Δ₁, Nat.card X = 2 ^ f) →
    ∀ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 4) →* G,
      Φ.ker = Subgroup.center _ → Φ.range = gen Δ₁ →
      (∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub ((Unitary.rootDatum
        (card_galoisField_two_mul hf) 4).rootGroup (unitaryLongRoot 4 (by norm_num))) g).map Φ) →
      Output G R

theorem oaDegenerateInput_of (hSU : OADegSUInput) : OADegenerateInput := by
  intro G _ R A A₀ Δ₁ Δ₂ hset hdeg
  have hD : DegOA R A A₀ Δ₁ Δ₂ := ⟨hset, hdeg⟩
  obtain ⟨f, hf, hcard, hsp | hsu⟩ := hD.tim90 hD.o3
  · obtain ⟨Φ, hΦ, hrange, hΔ⟩ := hsp
    exact hD.output_sp hf hcard Φ hΦ hrange hΔ
  · obtain ⟨Φ, hker, hrange, hΔ⟩ := hsu
    exact hSU G R A A₀ Δ₁ Δ₂ hD f hf hcard Φ hker hrange hΔ

end CaseOADeg

end CFSG.Timmesfeld.ARS
