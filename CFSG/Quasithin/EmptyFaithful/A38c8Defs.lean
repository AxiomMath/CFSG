module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique

@[expose] def InnerOnModO2 {Y : Type} [Group Y] (B : Subgroup Y) (t : Y) : Prop :=
  ∃ b ∈ B, ∀ x ∈ B, (t * x * t⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B

@[expose] def OutOddM24 : Prop :=
  Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
    (CFSG.Blueprint.NativeSporadic.Carrier .M24)))

@[expose] def J4L4Inner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N T B : Subgroup Y), N.Normal → IsSporadic .J4 ↥N →
    IsSylowTwoOf T ⊤ → B ≤ N → B ∈ lFamily T → T ≤ Subgroup.normalizer (B : Set Y) →
      IsPSL 4 2 1 (ModO2 B) → ∀ x ∈ T ⊓ N, InnerOnModO2 B x

@[expose] def SporadicL4Inner : Prop := OutOddM24 ∧ J4L4Inner

end CFSG.Quasithin.A38c8
