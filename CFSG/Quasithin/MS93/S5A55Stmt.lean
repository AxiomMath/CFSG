module

public import CFSG.Quasithin.MS93.S5A54Sp

public section

namespace CFSG.Quasithin.MS93.S5

@[expose] def Sp4Case55 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [CharP F 2] (R A₀ D Z : Subgroup (MSP.Sp4 F))
    (l : Submodule F (MSP.V4 F)),
    IsPGroup 2 R → candMax R = {A₀} → MSP.IsLine l → R ≤ MSP.stab l → A₀ ≤ MSP.qLine l →
    Nat.card F ^ 2 ≤ Nat.card A₀ →
    (∀ p₁ p₂ : Submodule F (MSP.V4 F), MSP.IsPoint p₁ → MSP.IsPoint p₂ →
      A₀ ≠ MSP.xPoint p₁ ⊔ MSP.xPoint p₂) →
    (Nat.card F = 2 → ¬ R ≤ commutator (MSP.Sp4 F)) →
    D ≤ R → R ≤ Subgroup.normalizer (D : Set (MSP.Sp4 F)) → Nat.card A₀ ≤ Nat.card D →
    ¬ IsCandSp R D → Z ≤ R →
    ((∃ c : Submodule F (MSP.V4 F), MSP.IsPoint c ∧ Z = MSP.xPoint c) ∨
      (Nat.card F ^ 2 ≤ Nat.card Z ∧ MSP.commSp Z ≤ MSP.fixSp Z ∧
        Module.finrank F (MSP.fixSp Z) ≤ 2) ∨
      (Nat.card F = 2 ∧ ∃ v₁ v₂ : MSP.V4 F, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
        MSP.form F v₁ v₂ = 0 ∧ MSP.transv v₁ 1 ∈ R ∧ MSP.transv v₂ 1 ∈ R ∧
        (MSP.transv v₁ 1 ∈ Z ∨ MSP.transv v₂ 1 ∈ Z ∨ MSP.transv v₁ 1 * MSP.transv v₂ 1 ∈ Z))) →
    ∃ g : MSP.Sp4 F,
      MSP.fixSp R ⊓ MSP.fixSp (A₀.map (MulAut.conj g⁻¹).toMonoidHom) = ⊥ ∧
      (commutator (MSP.Sp4 F) ≤ D.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z ∨
        (R.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z = ⊤ ∧ Nat.card D = Nat.card A₀ ∧
          Nat.card ↥(D ⊓ A₀) ≤ Nat.card F ^ 2))

end CFSG.Quasithin.MS93.S5
