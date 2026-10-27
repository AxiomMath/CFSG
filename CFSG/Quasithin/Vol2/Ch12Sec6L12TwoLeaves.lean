module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

@[expose] def A6Config {X : Type} [Group X] (Y F : Subgroup X) : Prop :=
  ⁅Y, Y⁆ = Y ∧ quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) ∧
    F ≤ pCoreOf 2 Y ∧ IsElemAbelian 2 F ∧ Y ≤ Subgroup.normalizer (F : Set X) ∧ ⁅F, Y⁆ = F

@[expose] def Char2LeviFamily (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = StatedLieTag.PSL ∧ n = 3 ∧ 1 ≤ f) ∨ (t = StatedLieTag.PSU ∧ n = 3 ∧ 2 ≤ f) ∨
    (t = StatedLieTag.PSp ∧ n = 2 ∧ 2 ≤ f) ∨ (t = StatedLieTag.G2 ∧ n = 0 ∧ 2 ≤ f) ∨
    (t = StatedLieTag.trialityD4 ∧ n = 0 ∧ 1 ≤ f) ∨
    (t = StatedLieTag.twistedF4 ∧ n = 0 ∧ Odd f ∧ 3 ≤ f) ∨ (t = StatedLieTag.Tits ∧ n = 0 ∧ f = 1)

@[expose] def LeviA6Free : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ), Char2LeviFamily t n f →
    LieModel X t n 2 f → ∀ (S : Sylow 2 X) (P : Subgroup X), P ≠ ⊤ →
      (t ≠ StatedLieTag.Tits → Subgroup.normalizer (S : Set X) ≤ P) →
      (t = StatedLieTag.Tits → (S : Subgroup X) ≤ P) →
      ∀ Y : Subgroup X, Y ≤ P → ∀ φ : ↥Y →* alternatingGroup (Fin 6),
        Function.Surjective φ → False

@[expose] def A6LocM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* ↥NativeSporadic.M22) →
    ∀ Y F : Subgroup X, A6Config Y F → Nat.card ↥F ≤ 16

@[expose] def A6LocM23 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* ↥NativeSporadic.M23) →
    ∀ Y F : Subgroup X, A6Config Y F → Nat.card ↥F ≤ 16

@[expose] def A6LocM24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* ↥NativeSporadic.M24) →
    ∀ Y F : Subgroup X, A6Config Y F → Nat.card ↥F ≤ 16

@[expose] def A6LocHS : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.HS) →
    ∀ Y F : Subgroup X, A6Config Y F → Nat.card ↥F ≤ 16

@[expose] def A6LocL52 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X StatedLieTag.PSL 5 2 1 →
    ∀ Y F : Subgroup X, A6Config Y F → Nat.card ↥F ≤ 16

@[expose] def A6LocJ2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J2) →
    ∀ Y F : Subgroup X, A6Config Y F → Nat.card ↥F < 16

end CFSG.Quasithin.H13.K1262Two
