module

public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin.SmithD37

@[expose] noncomputable def endCard {Q : Type} [CommGroup Q] (L : Subgroup (MulAut Q)) : ℕ :=
  Nat.card {φ : Q →* Q // ∀ l ∈ L, ∀ v, φ (l v) = l (φ v)}

structure Cls2F {Q : Type} [CommGroup Q] [Finite Q] (G L E : Subgroup (MulAut Q)) : Prop where
  exp : ∀ v : Q, v ^ 2 = 1
  hyp : B4Hyp G L
  a38 : A38Types ↥L
  a2 : IsA2 G E
  cubic : commSeries E 3 = ⊥
  off : Nat.card Q ≤ Nat.card E ^ 2 * Nat.card (fixV E)

end CFSG.Quasithin.SmithD37
