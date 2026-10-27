module

public import CFSG.Quasithin.Background.A3Structure315Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def IsLieChar2Big (S : Type) [Group S] : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ A315.IsLieChar2 k S

abbrev innAut (S : Type) [Group S] : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range

@[expose] def OutTwoNilpotentFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → A23List S →
    ∃ N : Subgroup (MulAut S), N.Normal ∧ innAut S ≤ N ∧ Odd ((innAut S).relIndex N) ∧
      ∀ α : MulAut S, ∃ k : ℕ, α ^ (2 ^ k) ∈ N

@[expose] def OddSylowNormalizerFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → A23List S →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → ∀ (d : MulAut S) (r : ℕ), r.Prime → r ≠ 2 →
      orderOf d = r → P.map d.toMonoidHom = P → (∃ x ∈ P, d x ≠ x) →
      (∀ y ∈ Subgroup.normalizer (P : Set S), d y * y⁻¹ ∈ P) →
      IsLieChar2Big S ∨ (r = 7 ∧ d ∈ innAut S ∧ Is3D4 2 1 S) ∨
        (r = 3 ∧ d ∈ innAut S ∧ IsSporadic .J2 S) ∨
        (r = 3 ∧ d ∈ innAut S ∧ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
          IsPSL 2 p 1 S)

@[expose] def LieOvergroupFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsLieChar2Big S →
    ∀ P : Subgroup S, IsSylowTwoOf P ⊤ →
      ∀ X : Subgroup S, P ≤ X → Group.IsSolvable ↥X → X ≤ Subgroup.normalizer (P : Set S)

end CFSG.Quasithin.H13
