module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open

@[expose] def AS_G_3_1_O2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Gm : Subgroup (MulAut V)), pCoreOf 2 Gm = ⊥ → ∀ (Δ₀ : Set (Subgroup V)), Δ₀.Nonempty →
    (∀ X ∈ Δ₀, Nat.card X = 2) →
    (∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map (g : MulAut V).toMonoidHom ∈ Δ₀) →
    (∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map (g : MulAut V).toMonoidHom = Y) →
    (∀ X ∈ Δ₀, 4 ≤ (transvGroup Gm X ⊓ pCoreOf 2 Gm).relIndex (transvGroup Gm X)) →
    ∀ (s : ℕ) (hs : 0 < s) (Δ : Fin s → Set (Subgroup V)),
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) → (⋃ i, Δ i) = Δ₀ → (∀ i, (Δ i).Nonempty) →
      (∀ i, ∀ X ∈ Δ i, ∀ g ∈ g31G Gm Δ₀, X.map (g : MulAut V).toMonoidHom ∈ Δ i) →
      (∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ g31G Gm Δ₀, X.map (g : MulAut V).toMonoidHom = Y) →
        (iSupIndep (fun i => g31V (Δ i)) ∧ (⨆ i, g31V (Δ i)) = g31V Δ₀ ∧
          iSupIndep (fun i => g31G Gm (Δ i)) ∧ (⨆ i, g31G Gm (Δ i)) = g31G Gm Δ₀ ∧
          (∀ i j, i ≠ j → ∀ a ∈ g31G Gm (Δ i), ∀ b ∈ g31G Gm (Δ j), a * b = b * a) ∧
          (∀ i j, i ≠ j → ∀ a ∈ g31G Gm (Δ i), ∀ v ∈ g31V (Δ j), a v = v) ∧
          ∀ i j, ∃ g ∈ Gm, (g31V (Δ i)).map (g : MulAut V).toMonoidHom = g31V (Δ j) ∧
            (g31G Gm (Δ i)).map (MulAut.conj g).toMonoidHom = g31G Gm (Δ j)) ∧
        ((∀ φ : ↥(g31V (Δ ⟨0, hs⟩)) ≃* ↥(g31V (Δ ⟨0, hs⟩)), ∃ g ∈ g31G Gm (Δ ⟨0, hs⟩),
            ∀ v : ↥(g31V (Δ ⟨0, hs⟩)), g (v : V) = ((φ v : ↥(g31V (Δ ⟨0, hs⟩))) : V)) ∧
          Δ ⟨0, hs⟩ = {X | X ≤ g31V (Δ ⟨0, hs⟩) ∧ Nat.card X = 2} ∧
          IsElemAbelian2 (g31G Gm (Δ ⟨0, hs⟩) ⊓
            fixingSubgroup (MulAut V) (g31V (Δ ⟨0, hs⟩) : Set V)) ∧
          ∀ d : ℕ, Nat.card (g31V (Δ ⟨0, hs⟩)) = 2 ^ d → ∀ X ∈ Δ ⟨0, hs⟩,
            Nat.card (transvGroup Gm X) = 2 ^ (d - 1) * Nat.card ↥(transvGroup Gm X ⊓
              fixingSubgroup (MulAut V) (g31V (Δ ⟨0, hs⟩) : Set V))) ∧
        8 ≤ Nat.card (g31V (Δ ⟨0, hs⟩))

end CFSG.Quasithin.ASInputs
