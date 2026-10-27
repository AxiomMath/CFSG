module

public import CFSG.Quasithin.Background.E6TwentyFour
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

open scoped commutatorElement

namespace CFSG.Quasithin.E6

open CFSG.Open

variable {G : Type} [Group G] {V : Subgroup G}

@[expose] def E624MarkedDecomposition (hV : IsElemAbelian 2 V) (M X : Subgroup G)
    (s : ℕ) (Y : Fin s → Subgroup (MulAut (IntMod V hV)))
    (Vs : Fin s → Subgroup (IntMod V hV)) (first : Fin s) : Prop :=
  ((⨆ index, Y index) = e624Y hV M X ∧ iSupIndep Y ∧
    ∀ index other, index ≠ other → ∀ left ∈ Y index, ∀ right ∈ Y other,
      left * right = right * left) ∧
  (fixV (e624Y hV M X) ⊓ commSub ⊤ (e624Y hV M X) = ⊥ ∧
    fixV (e624Y hV M X) ⊔ commSub ⊤ (e624Y hV M X) = ⊤) ∧
  ((⨆ index, Vs index) = commSub ⊤ (e624Y hV M X) ∧ iSupIndep Vs ∧
    ∀ index, commSub ⊤ (Y index) = Vs index ∧ commSub (Vs index) (Y index) = Vs index) ∧
  ((∀ automorphism ∈ autI hV M, ∀ index, ∃ other,
      (Y index).map (MulAut.conj automorphism).toMonoidHom = Y other) ∧
    ∀ index other, ∃ automorphism ∈ autI hV M,
      (Y index).map (MulAut.conj automorphism).toMonoidHom = Y other) ∧
  (autI hV X = Y first ∨
    (Nat.card (autI hV X) = 3 ∧ autI hV X ≤ Y first ∧
      Y first = Subgroup.closure {automorphism | ∃ conjugator ∈ Y first,
        ∃ element ∈ autI hV X, automorphism = conjugator * element * conjugator⁻¹} ∧
      Nat.card (Y first) = 21 ∧
      (∃ left ∈ Y first, ∃ right ∈ Y first, left * right ≠ right * left) ∧
      ∀ index, Nat.card (Vs index) = 8))

@[expose] def E625FullStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) →
    U ∈ gammaE64 V M → (E3.mQuot V U : ℕ∞) = E3.rParam V → 1 < E3.mQuot V U →
    E3.mQuot V U < E3.mParam (autI hV M) →
    ∃ X : Subgroup G,
      (X ≤ M ⊓ Subgroup.centralizer (U : Set G) ∧ IsCyclic X ∧
        Nat.card X = 2 ^ E3.mQuot V U - 1 ∧
        IsCyclic (autI hV X) ∧ Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1 ∧
        U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V ∧
        (∀ element ∈ ⁅V, X⁆, element ≠ 1 → ∀ conjugator ∈ X,
          conjugator * element = element * conjugator →
          conjugator ∈ Subgroup.centralizer (V : Set G)) ∧
        (∀ conjugator ∈ M ⊓ Subgroup.normalizer (V : Set G),
          conjugator ∈ Subgroup.normalizer (U : Set G) → ∀ element ∈ X,
          ∃ image ∈ X, conjugator * element * conjugator⁻¹ * image⁻¹ ∈
            Subgroup.centralizer (V : Set G))) ∧
      ∃ (s : ℕ) (Y : Fin s → Subgroup (MulAut (IntMod V hV)))
        (Vs : Fin s → Subgroup (IntMod V hV)) (first : Fin s),
        E624MarkedDecomposition hV M X s Y Vs first ∧ autI hV M = Y first ∧
        (Nat.card (autI hV M) = 21 ∧
          ∃ left ∈ autI hV M, ∃ right ∈ autI hV M, left * right ≠ right * left) ∧
        (Nat.card V = 8 ∧ Nat.card U = 2) ∧ T ⊓ Subgroup.centralizer (V : Set G) = T

end CFSG.Quasithin.E6
