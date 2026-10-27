module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Desc1614Three (D : Data G) (V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (U : Subgroup G) : Prop :=
  ∃ t ∈ D.M, t ^ 2 ∈ centralizer (V : Set G) ∧ t ∉ centralizer (V : Set G) ∧
    U = V ⊓ centralizer ({t} : Set G) ∧
    D.M ⊓ centralizer (U : Set G) = (D.M ⊓ centralizer (V : Set G)) ⊔ zpowers t ∧
    ∀ z ∈ lBar ⊥ V hV L, (∀ y ∈ lBar ⊥ V hV L, y * z = z * y) → z ≠ 1 →
      ∀ s ∈ barSub ⊥ V hV (zpowers t), s ≠ 1 → s * z * s⁻¹ = z⁻¹

@[expose] noncomputable def Residual1614Three (D : Data G) (V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  Case168_3 D ⊥ V hV L ∧ (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 = 3 ∧
    ∀ U : Subgroup G, U ≤ V → E3.mQuot V U = D.k + 2 → ¬ centralizer (U : Set G) ≤ D.M →
      Desc1614Three D V L hV U

@[expose] noncomputable def Residual1614Eleven (D : Data G) (V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  Case168_11 D ⊥ V hV L ∧
    ∀ U : Subgroup G, U ≤ V → E3.mQuot V U = D.k + 2 → ¬ centralizer (U : Set G) ≤ D.M →
      ∃ t ∈ D.M, t ^ 2 ∈ centralizer (V : Set G) ∧ t ∉ centralizer (V : Set G) ∧
        U ≤ V ⊓ centralizer ({t} : Set G) ∧ E3.mQuot V (V ⊓ centralizer ({t} : Set G)) = 3

@[expose] noncomputable def R16_14Corr (D : Data G) : Prop :=
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    ((D.k + 2 : ℕ) : ℕ∞) ≤ rMV D.M V ∧
      (rMV D.M V = ((D.k + 2 : ℕ) : ℕ∞) →
        Residual1614Three D V L hV ∨ Residual1614Eleven D V L hV)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
