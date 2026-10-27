module

public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Defs
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBc17

@[expose] def StdPositionStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {L B : Subgroup G} {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2], 4 ≤ Fintype.card F → ∀ (α : ↥L →* SL2 F), Function.Surjective α →
      α.ker = CFSG.pCore 2 ↥L → IsBorelOfBlock L B →
        ∃ g₀ : G, g₀ ∈ L ∧ (∀ x : G, x ∈ conjSub g₀⁻¹ B → x ∈ L) ∧
          ∀ g : SL2 F, g ∈ borelSub F ↔ ∃ (x : G) (hx : x ∈ L), x ∈ conjSub g₀⁻¹ B ∧ α ⟨x, hx⟩ = g

@[expose] def CocycleStatement : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2], 4 ≤ Fintype.card F →
    ∀ d : SL2 F → (Fin 2 → F),
      (∀ g h : SL2 F, d (g * h) = d g + (g : Matrix (Fin 2) (Fin 2) F).mulVec (d h)) →
        (∀ b ∈ borelSub F, d b = 0) → ∀ g : SL2 F, d g = 0

@[expose] def CenterStatement : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2], 4 ≤ Fintype.card F →
    ∀ z ∈ borelSub F, (∀ b ∈ borelSub F, z * b = b * z) → z = 1

@[expose] def InnerAutStatement : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2], 4 ≤ Fintype.card F →
    ∀ φ : MulAut (SL2 F), (∀ b ∈ borelSub F, φ b * b⁻¹ ∈ upperSub F) →
      ∃ g : SL2 F, ∀ x : SL2 F, φ x = g * x * g⁻¹

@[expose] def LeUpperStatement : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2], 4 ≤ Fintype.card F →
    ∀ {W : Subgroup (SL2 F)}, IsPGroup 2 W → upperSub F ≤ Subgroup.normalizer (W : Set (SL2 F)) →
      W ≤ upperSub F

end SBc17

end CFSG.Quasithin
