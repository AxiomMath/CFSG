module

public import CFSG.Monster.GMS.S365Facts
public import CFSG.Monster.GMS.Leech.Linear

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

@[expose] def InIm (g : Co1) (v : Fin 24 → ZMod 2) : Prop := ∃ p, v = p + co1Act g p

@[expose] def Pat0 (a b ω ν : Fin 24 → ZMod 2) : Prop :=
  ν ∈ co1Orbit 2 ∧ ν + a ∈ co1Orbit 0 ∧ ν + b ∈ co1Orbit 0 ∧ ν + a + b ∈ co1Orbit 0 ∧
    ν + ω ∈ co1Orbit 2 ∧ ν + ω + a ∈ co1Orbit 2 ∧ ν + ω + b ∈ co1Orbit 2 ∧
    ν + ω + a + b ∈ co1Orbit 2

@[expose] def Co1NoPatternIm : Prop :=
  ∀ s : Co1, IsCo1TwoA s → ∀ a b ω : Fin 24 → ZMod 2, FourPattern a b ω → InIm s a → InIm s b →
    InIm s ω → False

@[expose] def Co1WitnessS : Prop :=
  ∀ a b ω : Fin 24 → ZMod 2, FourPattern a b ω → ∃ e₀ : Fin 24 → ZMod 2, ∃ g₁ g₂ : Co1,
    (co1Act g₁ a = a ∧ co1Act g₁ b = b ∧ co1Act g₁ ω = ω) ∧
    (co1Act g₂ a = a ∧ co1Act g₂ b = b ∧ co1Act g₂ ω = ω) ∧
    ∀ ν, Pat0 a b ω ν → ν ≠ e₀ → ∃ g ∈ ({g₁, g₂} : Set Co1), ν + co1Act g ν ≠ 0 ∧
      ¬ Pat0 a b ω (ν + co1Act g ν)

@[expose] def Co1FourU2 : Prop :=
  ∀ r s : Co1, IsCo1TwoA r → IsCo1TwoA s → r * s = s * r → IsCo1TwoA (r * s) →
    ∃ v₁ v₂ : Fin 24 → ZMod 2, v₁ ≠ v₂ ∧ v₁ ∈ co1Orbit 2 ∧ v₂ ∈ co1Orbit 2 ∧
      InIm r v₁ ∧ InIm s v₁ ∧ InIm (r * s) v₁ ∧ InIm r v₂ ∧ InIm s v₂ ∧ InIm (r * s) v₂

theorem Pat0.map {a b ω ν : Fin 24 → ZMod 2} (g : Co1) (h : Pat0 a b ω ν) :
    Pat0 (g • a) (g • b) (g • ω) (g • ν) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have m0 : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 0 → g • u ∈ co1Orbit 0 :=
    fun hu => Leech.co1Act_mem_co1Orbit hu g
  have m2 : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 2 → g • u ∈ co1Orbit 2 :=
    fun hu => Leech.co1Act_mem_co1Orbit hu g
  refine ⟨m2 h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add]; exact m0 h2
  · rw [← smul_add]; exact m0 h3
  · rw [← smul_add, ← smul_add]; exact m0 h4
  · rw [← smul_add]; exact m2 h5
  · rw [← smul_add, ← smul_add]; exact m2 h6
  · rw [← smul_add, ← smul_add]; exact m2 h7
  · rw [← smul_add, ← smul_add, ← smul_add]; exact m2 h8

theorem Pat0.map_iff {a b ω ν : Fin 24 → ZMod 2} (g : Co1) :
    Pat0 (g • a) (g • b) (g • ω) (g • ν) ↔ Pat0 a b ω ν := by
  refine ⟨fun h => ?_, Pat0.map g⟩
  have := Pat0.map g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul, inv_smul_smul, inv_smul_smul] at this

end S365

end CFSG.Monster.GMS
