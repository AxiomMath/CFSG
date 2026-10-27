module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def LandazuriSeitzL2Even : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
      (ρ : projSL 2 (GaloisField 2 f) →* (V →ₗ[ZMod p] V)), Function.Injective ρ →
        2 ^ f - 1 ≤ Module.finrank (ZMod p) V ∧
          ∀ t : projSL 2 (GaloisField 2 f), orderOf t = 2 →
            (2 ^ f - 2) / 2 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1))

@[expose] def BlackburnRankTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (P : Type) [Group P] [Finite P], IsPGroup p P →
    (∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
      (∃ s : Finset P, s.card ≤ 3 ∧ Subgroup.closure (s : Set P) = ⊤) ∧
        ((∀ s : Finset P, s.card ≤ 2 → Subgroup.closure (s : Set P) ≠ ⊤) →
          ∃ Z₀ : Subgroup P, Z₀.Characteristic ∧ frattini P ≤ Z₀ ∧
            (frattini P).relIndex Z₀ = p)

@[expose] def TorusSelfCentralizingL2 : Prop :=
  ∀ (f : ℕ), 3 ≤ f → ∀ T : Subgroup (projSL 2 (GaloisField 2 f)), IsCyclic T →
    (Nat.card T = 2 ^ f - 1 ∨ Nat.card T = 2 ^ f + 1) →
      ∀ φ : MulAut (projSL 2 (GaloisField 2 f)), (∀ t ∈ T, φ t = t) →
        ∃ t ∈ T, ∀ x, φ x = t * x * t⁻¹

end CFSG.RankThree.PartTwo.KFacts
