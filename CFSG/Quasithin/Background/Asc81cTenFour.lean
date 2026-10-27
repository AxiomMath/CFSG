module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin

namespace Asc81c

variable {W : Type*} [CommGroup W]

@[expose] def Hyp101 (G X : Subgroup (MulAut W)) : Prop :=
  X ≤ G ∧ X ≠ ⊥ ∧ IsCyclic X ∧ Odd (Nat.card X) ∧
    (∀ v ∈ commSub ⊤ X, v ≠ 1 → ∀ w ∈ commSub ⊤ X, w ≠ 1 →
      ∃! x : X, (x : MulAut W) v = w) ∧
    ∀ g ∈ G, (fixV X).map (g : MulAut W).toMonoidHom = fixV X → ∀ x ∈ X, g * x * g⁻¹ ∈ X

@[expose] def Hyp102 (G X : Subgroup (MulAut W)) : Prop :=
  Hyp101 G X ∧ rk (commSub ⊤ X) < E3.mParam G

@[expose] def Thm104 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut W)) (Ω : Set (Subgroup (MulAut W))),
      (∀ X ∈ Ω, Hyp102 G X) →
      (∀ g ∈ G, ∀ X ∈ Ω, X.map (MulAut.conj g).toMonoidHom ∈ Ω) →
      ∃ (n : ℕ) (L : Fin n → Subgroup (MulAut W)),
        (⨆ i, L i) = sSup Ω ∧ iSupIndep L ∧
        (∀ i j, i ≠ j → ∀ a ∈ L i, ∀ b ∈ L j, a * b = b * a) ∧
        (∀ g ∈ G, ∀ i, ∃ j, (L i).map (MulAut.conj g).toMonoidHom = L j) ∧
        (⨆ i, commSub ⊤ (L i)) = commSub ⊤ (sSup Ω) ∧
        iSupIndep (fun i => commSub ⊤ (L i)) ∧
        ∀ X ∈ Ω, (∃ i, X = L i) ∨
          (∃ i, X ≤ L i ∧ Nat.card (L i) = 21 ∧ ∃ a ∈ L i, ∃ b ∈ L i, a * b ≠ b * a)

end Asc81c

end CFSG.Quasithin
