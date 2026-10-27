module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNF

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small

@[expose] def SmallNFStatement : Prop :=
  ∀ {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] (D : D4Datum G K),
    4 ≤ Nat.card K →
    ∀ {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
      (ρ : Representation K G X),
      (∀ S : Submodule K X, (∀ g : G, ∀ x ∈ S, ρ g x ∈ S) → S = ⊥ ∨ S = ⊤) →
      (∃ g : G, ρ g ≠ 1) → Module.finrank K X ≤ 16 →
      ∃ (j : ℕ) (C : Finset (Fin 4 → ZMod (Nat.card Kˣ)))
        (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X),
        2 ^ j < Nat.card Kˣ ∧ NFType j C ∧ NF D ρ j C b

@[expose] def NFIsoStatement : Prop :=
  ∀ {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] (D : D4Datum G K),
    ∀ {X X' : Type} [AddCommGroup X] [Module K X] [AddCommGroup X'] [Module K X']
      (ρ : Representation K G X) (ρ' : Representation K G X') (j : ℕ)
      (C : Finset (Fin 4 → ZMod (Nat.card Kˣ))) (b : (Fin 4 → ZMod (Nat.card Kˣ)) → X)
      (b' : (Fin 4 → ZMod (Nat.card Kˣ)) → X'),
      NF D ρ j C b → NF D ρ' j C b' →
        ∃ e : X ≃ₗ[K] X', ∀ (g : G) (x : X), e (ρ g x) = ρ' g (e x)

end CFSG.RankThree.GF2n.Stroth80.Tri

end
