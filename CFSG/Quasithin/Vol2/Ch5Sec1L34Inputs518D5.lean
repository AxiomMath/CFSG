module

public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def L34TwoParabolicFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 2 → ∀ S₀ : Subgroup X,
    IsSylowTwoOf S₀ ⊤ →
    ∃ R₂ R₃ : Subgroup X, R₂ ≠ R₃ ∧
      (∀ R : Subgroup X, (R = R₂ ∨ R = R₃) →
        R ≤ S₀ ∧ Subgroup.normalizer (S₀ : Set X) ≤ Subgroup.normalizer (R : Set X) ∧
        IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
        (∃ π : ↥(Subgroup.normalizer (R : Set X)) →*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
          Function.Surjective π ∧ π.ker = R.subgroupOf (Subgroup.normalizer (R : Set X))) ∧
        oTwoUpper (Subgroup.normalizer (R : Set X)) = Subgroup.normalizer (R : Set X) ∧
        ∀ α : MulAut X, Odd (orderOf α) → S₀.map α.toMonoidHom = S₀ →
          R.map α.toMonoidHom = R) ∧
      Subgroup.normalizer (R₂ : Set X) ⊔ Subgroup.normalizer (R₃ : Set X) = ⊤ ∧
      ∀ α : MulAut X, S₀.map α.toMonoidHom = S₀ →
        (R₂.map α.toMonoidHom = R₂ ∨ R₂.map α.toMonoidHom = R₃) ∧
        (R₃.map α.toMonoidHom = R₂ ∨ R₃.map α.toMonoidHom = R₃)

@[expose] def A314FiveNormFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    A314Statement T B L → Nat.card D = 5 → D ≤ Subgroup.normalizer (L : Set Y) →
    T ≤ Subgroup.normalizer (L : Set Y) → T ≤ Subgroup.normalizer (B : Set Y) →
    (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) →
    (∃ b ∈ B, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y) ∧
      ∀ d ∈ D, d * b = b * d) →
    D ≤ Subgroup.normalizer (B : Set Y)

end CFSG.Quasithin.H13
