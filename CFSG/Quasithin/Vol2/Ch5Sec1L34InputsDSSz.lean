module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def F112SecondNoSzFact : Prop :=
  ∀ α : RankTwoAmalgam.{0},
    (IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 1) ∨ IsAmalgamOfGroup α (IsSp4Over 1) ∨
      IsAmalgamOfGroup α (IsG2Over 1) ∨ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 1) ∨
      IsAmalgamOfGroup α (IsTwistedF4Over 1) ∨
      IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∨
      IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 1) ∨
      IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∨
      IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∨
      IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∨
      IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∨
      IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∨
      (∃ f : ℕ, 1 ≤ f ∧ IsU4ExtTwo f α)) →
    ∀ a : ℕ, 1 ≤ a →
      (∀ L : Subgroup α.G1, IsEmpty (oTwoQuot ↥L ≃* ↥(Sz a))) ∧
        ∀ L : Subgroup α.G2, IsEmpty (oTwoQuot ↥L ≃* ↥(Sz a))


@[expose] def U4ExtTwoVertexFact : Prop :=
  ∀ (f : ℕ) (α : RankTwoAmalgam.{0}), 1 ≤ f → IsU4ExtTwo f α →
    (∀ (L : Subgroup α.G1) (N : Subgroup ↥L) [N.Normal], IsSimpleGroup (↥L ⧸ N) →
        (∃ x y : ↥L ⧸ N, x * y ≠ y * x) → 3 ∣ Nat.card (↥L ⧸ N)) ∧
      ∀ (L : Subgroup α.G2) (N : Subgroup ↥L) [N.Normal], IsSimpleGroup (↥L ⧸ N) →
        (∃ x y : ↥L ⧸ N, x * y ≠ y * x) → 3 ∣ Nat.card (↥L ⧸ N)

end CFSG.Quasithin.H13
