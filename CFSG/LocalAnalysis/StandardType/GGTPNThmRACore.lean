module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreLin
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreUni

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem split_or_fieldType_of_ggKacRA {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J) {labX : LargeEvenLabel}
    (hRA : GGKacRA labX p) (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    (∃ (a : ℕ) (ds : List ℕ), labX.rank + 1 = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
        (∀ x ∈ ds, x = 1 ∨ (labX.tag = .twA ∧ labX.n = 1 ∧ (x = 2 ∨ x = 3))) ∧
        ((LargeEvenInLambda2 ⟨labX.tag, a - 1, labX.n⟩ ∧
            GGHasLabel ⟨labX.tag, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
          (labX.tag = .twA ∧ a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, labX.n⟩ ∧
            GGHasLabel ⟨.A, 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)))) ∨
    (2 ≤ (labX.rank + 1) / p ∧ Nat.card A ≤ p ^ ((labX.rank + 1) / p + 1) ∧
      (((labX.tag = .A ∨ (labX.rank + 1) / p = 2) ∧
          LargeEvenInLambda2 ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ ∧
          GGHasLabel ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (labX.tag = .twA ∧ 3 ≤ (labX.rank + 1) / p ∧
          LargeEvenInLambda2 ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩ ∧
          GGHasLabel ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩
            (↥J ⧸ Subgroup.center ↥J)))) := by
  rcases hRA with h | h
  · exact split_or_fieldType_of_ggKacRA_linear hp hloc h8 h.1 (Or.inl h) hm
  · exact split_or_fieldType_of_ggKacRA_unitary hp hloc h8 h.1 (Or.inr h) hm

end CFSG.StandardType

end
