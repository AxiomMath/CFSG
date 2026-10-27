module

public import CFSG.Quasithin.Background.E6Gamma

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open

variable {G : Type} [Group G] {V : Subgroup G}

@[expose] noncomputable def e624Y (hV : IsElemAbelian 2 V) (M X : Subgroup G) :
    Subgroup (MulAut (IntMod V hV)) :=
  Subgroup.closure {ψ | ∃ φ ∈ autI hV M, ∃ ξ ∈ autI hV X, ψ = φ * ξ * φ⁻¹}

theorem autI_le_e624Y (hV : IsElemAbelian 2 V) (M X : Subgroup G) :
    autI hV X ≤ e624Y hV M X :=
  fun ξ hξ => Subgroup.subset_closure ⟨1, (autI hV M).one_mem, ξ, hξ, by simp⟩

theorem e624Y_le (hV : IsElemAbelian 2 V) {M X : Subgroup G} (hXM : X ≤ M) :
    e624Y hV M X ≤ autI hV M := by
  refine (Subgroup.closure_le _).2 ?_
  rintro ψ ⟨φ, hφ, ξ, hξ, rfl⟩
  exact (autI hV M).mul_mem ((autI hV M).mul_mem hφ (autI_mono hV hXM hξ))
    ((autI hV M).inv_mem hφ)

@[expose] def E624Concl (hV : IsElemAbelian 2 V) (M X : Subgroup G) : Prop :=
  ∃ (s : ℕ) (Y : Fin s → Subgroup (MulAut (IntMod V hV))) (Vs : Fin s → Subgroup (IntMod V hV)),
    ((⨆ i, Y i) = e624Y hV M X ∧ iSupIndep Y ∧
      ∀ i j, i ≠ j → ∀ a ∈ Y i, ∀ b ∈ Y j, a * b = b * a) ∧
    (fixV (e624Y hV M X) ⊓ commSub ⊤ (e624Y hV M X) = ⊥ ∧
      fixV (e624Y hV M X) ⊔ commSub ⊤ (e624Y hV M X) = ⊤) ∧
    ((⨆ i, Vs i) = commSub ⊤ (e624Y hV M X) ∧ iSupIndep Vs ∧
      ∀ i, commSub ⊤ (Y i) = Vs i ∧ commSub (Vs i) (Y i) = Vs i) ∧
    ((∀ φ ∈ autI hV M, ∀ i, ∃ j, (Y i).map (MulAut.conj φ).toMonoidHom = Y j) ∧
      ∀ i j, ∃ φ ∈ autI hV M, (Y i).map (MulAut.conj φ).toMonoidHom = Y j) ∧
    ((∃ i, autI hV X = Y i) ∨
      (Nat.card (autI hV X) = 3 ∧ ∃ i, autI hV X ≤ Y i ∧
        Y i = Subgroup.closure {ψ | ∃ φ ∈ Y i, ∃ ξ ∈ autI hV X, ψ = φ * ξ * φ⁻¹} ∧
        Nat.card (Y i) = 21 ∧ (∃ a ∈ Y i, ∃ b ∈ Y i, a * b ≠ b * a) ∧
        ∀ j, Nat.card (Vs j) = 8))

@[expose] def E624Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U X : Subgroup G) (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) →
    U ∈ gammaE64 V M → (E3.mQuot V U : ℕ∞) = E3.rParam V → 1 < E3.mQuot V U →
    E3.mQuot V U < E3.mParam (autI hV M) →
    X ≤ M ⊓ Subgroup.centralizer (U : Set G) → IsCyclic (autI hV X) →
    Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1 →
    U ⊓ ⁅V, X⁆ = ⊥ → U ⊔ ⁅V, X⁆ = V →
    (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v = v * x → x ∈ Subgroup.centralizer (V : Set G)) →
    (∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x ∈ X, ∃ y ∈ X, g * x * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
    E624Concl hV M X

end E6

end CFSG.Quasithin
