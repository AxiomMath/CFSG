module

public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import Mathlib.Logic.Relation

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

abbrev ggWeylD (k : ℕ) : Type := (coxeterMatrix (isFiniteType_cartanD k)).Group

@[expose] def GGDReflRoot (k : ℕ) (t : ggWeylD k) (γ : Fin k → ℤ) : Prop :=
  ∃ (w : ggWeylD k) (i : Fin k), t = w * (coxeterMatrix (isFiniteType_cartanD k)).simple i * w⁻¹ ∧
    toStdD k (weylAction (isFiniteType_cartanD k) w (Pi.single i 1)) = γ

@[expose] def GGDSameSupp (k : ℕ) (t t' : ggWeylD k) : Prop :=
  ∃ (a b : Fin k) (s : ℤ), a ≠ b ∧ (s = 1 ∨ s = -1) ∧
    GGDReflRoot k t (Pi.single a 1 + Pi.single b s) ∧
    GGDReflRoot k t' (Pi.single a 1 - Pi.single b s)

@[expose] def GGDDisjSupp (k : ℕ) (t t' : ggWeylD k) : Prop :=
  ∃ (a b c d : Fin k) (s s' u u' : ℤ), a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧ (u = 1 ∨ u = -1) ∧ (u' = 1 ∨ u' = -1) ∧
    GGDReflRoot k t (Pi.single a s + Pi.single b s') ∧
    GGDReflRoot k t' (Pi.single c u + Pi.single d u')

@[expose] def ggDRootSet (k : ℕ) : Set (Fin k → ℤ) :=
  {γ | ∃ (a b : Fin k) (s t : ℤ), a ≠ b ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    γ = Pi.single a s + Pi.single b t}

@[expose] def ggDDot {k : ℕ} (u v : Fin k → ℤ) : ℤ := ∑ a, u a * v a

@[expose] def ggDReflect {k : ℕ} (γ δ : Fin k → ℤ) : Fin k → ℤ := δ - ggDDot δ γ • γ

@[expose] def GGDSubsys (k : ℕ) (Φ : Set (Fin k → ℤ)) : Prop :=
  Φ ⊆ ggDRootSet k ∧ ∀ γ ∈ Φ, ∀ δ ∈ Φ, ggDReflect γ δ ∈ Φ

@[expose] def GGDIrred {k : ℕ} (Φ : Set (Fin k → ℤ)) : Prop :=
  ∀ γ ∈ Φ, ∀ δ ∈ Φ,
    Relation.ReflTransGen (fun u v => u ∈ Φ ∧ v ∈ Φ ∧ ggDDot u v ≠ 0) γ δ

end CFSG.StandardType

end
