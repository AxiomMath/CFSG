module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

@[expose] def KU4Delta : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 2 ≤ n → IsU4 Y n →
    ∀ (S : Subgroup Y) (R : Subgroup (MulAut Y)) (p : ℕ),
      IsSylowIn 2 S ⊤ → IsPGroup 2 R → (∀ r ∈ R, S.map r.toMonoidHom = S) →
      p.Prime → p ∣ 2 ^ n + 1 →
      ∃ (P Y₀ : Subgroup Y),
        S17.IsMaxParabolicOver (⊤ : Subgroup Y) S P ∧
        (∀ r ∈ R, P.map r.toMonoidHom = P) ∧
        ⁅Opp 2 P, Opp 2 P⁆ = Opp 2 P ∧ IsL2 (Bar2 (Opp 2 P)) n ∧
        Nat.card Y₀ = p ∧ Y₀ ≤ Subgroup.normalizer (S : Set Y) ∧
        (∀ r ∈ R, (S ⊔ Y₀).map r.toMonoidHom = S ⊔ Y₀) ∧
        ∃ E : Subgroup Y, E ≤ Opp 2 P ⊔ Y₀ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2

@[expose] def KU5Delta : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsU5 Y 2 →
    ∀ (S : Subgroup Y) (R : Subgroup (MulAut Y)),
      IsSylowIn 2 S ⊤ → IsPGroup 2 R → (∀ r ∈ R, S.map r.toMonoidHom = S) →
      ∃ P : Subgroup Y,
        S17.IsMaxParabolicOver (⊤ : Subgroup Y) S P ∧
        (∀ r ∈ R, P.map r.toMonoidHom = P) ∧
        ⁅Opp 2 P, Opp 2 P⁆ = Opp 2 P ∧ CFSG.Open.IsQuasisimple (Bar2 (Opp 2 P)) ∧
        IsU3 (Bar2 (Opp 2 P)) 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
