module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.A38c10

open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

@[expose] def MSGat {G : Type} [Group G] (L S Vp Yp Y₁ Y₂ P : Subgroup G) (ψ : ↥P →* SLt 3)
    (q : G) : Prop :=
  P ≤ L ∧ S ⊓ L ≤ P ∧ P ≠ L ∧ (∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
    (∀ X : Subgroup G, S ⊓ L ≤ X → X ≤ L → X ≠ L → Yp ≤ X → ¬ P ≤ X) ∧
    (Y₁ ≤ P ∨ Y₂ ≤ P) ∧ Function.Surjective ψ ∧ (∀ x : ↥P, ψ x = 1 → (x : G) ∈ S ⊓ L) ∧
    q ∈ Vp ∧ q ≠ 1 ∧ (∀ a ∈ P, a * q * a⁻¹ = q) ∧ q ∈ ⁅Vp, oTwoUpper P⁆

@[expose] def Pof {G : Type} [Group G] (L : Subgroup G) (α : ↥L →* SLt 4) (k : ℕ) : Subgroup G :=
  Subgroup.map L.subtype ((QI 4 {k}).comap α)

theorem mem_Pof {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* SLt 4} {k : ℕ} (x : ↥L) :
    (x : G) ∈ Pof L α k ↔ α x ∈ QI 4 {k} := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem Pof_le {G : Type} [Group G] (L : Subgroup G) (α : ↥L →* SLt 4) (k : ℕ) :
    Pof L α k ≤ L :=
  Subgroup.map_subtype_le _

@[expose] def MSG2 {G : Type} [Group G] (L S Vp Yp Y₁ Y₂ : Subgroup G) : Prop :=
  ∃ α : ↥L →* SLt 4, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
    (∀ x : ↥L, (x : G) ∈ S ⊓ L ↔ α x ∈ Ut 4) ∧
    (∃ (ψ : ↥(Pof L α 1) →* SLt 3) (q : G), MSGat L S Vp Yp Y₁ Y₂ (Pof L α 1) ψ q) ∧
    (∃ (ψ : ↥(Pof L α 3) →* SLt 3) (q : G), MSGat L S Vp Yp Y₁ Y₂ (Pof L α 3) ψ q)

end CFSG.Quasithin.A38c10
