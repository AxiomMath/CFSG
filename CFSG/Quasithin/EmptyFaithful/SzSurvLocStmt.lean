module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocDefs
public import CFSG.Quasithin.Recognition.F112J2Reduce

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def F112R1PlusLocStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
      ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
    (∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) → F112SurvivorLoc K1 L2 S

@[expose] def F112R1aLocStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
      ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
    IsL2Quot 2 (OTwoQuot K1) → Survivor10Loc K1 L2 S ∨ Survivor11Loc K1 L2 S

@[expose] def F112R1bLocStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K1 L2 S Zs : Subgroup G), R1SettingLegacyBare K1 L2 S Zs →
    (⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ →
      ∀ u ∈ S, u * u = 1 → (∀ s ∈ S, u * s = s * u) → u ∈ Zs) →
    IsL2Quot 3 (OTwoQuot K1) → Survivor4LegacyBare K1 L2 S

theorem f112R1PlusLoc_of_R1abcLoc (hR1a : F112R1aLocStatement) (hR1b : F112R1bLocStatement)
    (hR1c : F112R1cStatementLegacyBare) : F112R1PlusLocStatement := by
  intro G _ _ K1 L2 S Zs hset hZS hbender
  by_cases h2 : IsL2Quot 2 (OTwoQuot K1)
  · exact Or.inr (hR1a G K1 L2 S Zs hset hZS h2)
  · by_cases h3 : IsL2Quot 3 (OTwoQuot K1)
    · exact Or.inl (hR1b G K1 L2 S Zs hset hZS h3)
    · exact (hR1c G K1 L2 S Zs hset hbender h2 h3).elim

end CFSG.Quasithin
