module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def ActionDataG (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (m : ℕ) (φ : ↥N →* Equiv.Perm (Fin m)), N.Normal ∧
    (∃ k : ℕ, N.index = 2 ^ k) ∧ 5 ≤ m ∧ IsPGroup 2 ↥φ.ker ∧ alternatingGroup (Fin m) ≤ φ.range

@[expose] def ActionData {Q : Type} [Group Q] (Y : Subgroup Q) : Prop := ActionDataG ↥Y

@[expose] def PerfCore {Q : Type} [Group Q] (P Y : Subgroup Q) : Prop :=
  perfectCore Y ≠ ⊥ ∧ perfectCore Y ∈ cComp (perfectCore Y) ∧ perfectCore Y ⊔ P = Y

@[expose] def MLDOver (Q : Type) [Group Q] [Finite Q] : Prop :=
  ∀ P : Subgroup Q, IsSylowTwoOf P ⊤ →
    Nat.card ↥(centerOf P) = 2 ∧
    ∀ W : Subgroup Q, W ≤ centerOf P → W ≠ ⊥ → ∀ Y : Subgroup Q, P ≤ Y → Y ≠ ⊤ →
      Subgroup.centralizer (W : Set Q) < Y → ActionData Y

@[expose] def MLDAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic s Q → MLDOver Q

end CFSG.Quasithin.S151S9U
