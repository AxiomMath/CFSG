module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveBCoordDense {G : Type} [Group G] {Bs : Subgroup G} {n p : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n) (D : Subgroup G) : Prop :=
  ∀ z : ↥Bs, (z : G) ∈ D → z ≠ 1 → eta z i0 = 1 →
    ∀ i, i ≠ i0 → eta z i ≠ 1 ∧ ∀ j, j ≠ i0 → eta z j = eta z i ∨ eta z j = (eta z i)⁻¹

@[expose] def GGSecFiveBCoordSparse {G : Type} [Group G] {Bs : Subgroup G} {n p : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n) (D : Subgroup G) : Prop :=
  ∀ z : ↥Bs, (z : G) ∈ D → z ≠ 1 → eta z i0 = 1 →
    ∃ i, i ≠ i0 ∧ ∀ j, j ≠ i0 → j ≠ i → eta z j = 1

@[expose] def GGSecFiveBCoordBJDenseLabel (n p : ℕ) (lab labJ : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .twD) ∧ p ∣ 2 ^ lab.n - 1 ∧
      labJ = ⟨.A, n - 2, lab.n⟩) ∨
    ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .twD ∨ lab.tag = .D) ∧ p ∣ 2 ^ lab.n + 1 ∧
      labJ = ⟨.twA, n - 2, lab.n⟩ ∧ ¬ (n = 5 ∧ lab.n = 1)) ∨
    (lab.tag = .A ∧ labJ = ⟨.A, n - 2, 2⟩)

@[expose] def GGSecFiveBCoordBJSparseLabel (n p : ℕ) (lab labJ : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧
      (labJ = ⟨.C, n - 2, lab.n⟩ ∨ n = 4 ∧ lab.n = 1 ∧ labJ = ⟨.B2der, 0, 1⟩)) ∨
    (lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1 ∧ labJ = ⟨.twD, n - 1, lab.n⟩) ∨
    (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1 ∧ labJ = ⟨.D, n - 1, lab.n⟩) ∨
    (lab.tag = .D ∧ labJ = ⟨.twD, n - 1, 1⟩) ∨
    (lab.tag = .A ∧ labJ = ⟨.A, lab.rank - 2, 1⟩)

@[expose] def GGSecFiveBCoordBJDenseLabelCore {G : Type} [Group G] (L : Subgroup G) (n p : ℕ)
    (lab labJ : LargeEvenLabel) : Prop :=
  GGSecFiveBCoordBJDenseLabel n p lab labJ ∨
    ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D) ∧ n = 5 ∧ lab.n = 1 ∧
      labJ = ⟨.twA, 3, 1⟩ ∧ Subgroup.center ↥L ≠ ⊥)

end CFSG.StandardType

end
