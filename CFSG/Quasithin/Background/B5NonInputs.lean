module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def IsL345Type (X : Type) [Group X] : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ↥(StatedSL 3 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧ Nonempty (X ≃* ↥(StatedSL 4 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧ Nonempty (X ≃* ↥(StatedSL 5 K)))

@[expose] def AsA21SQTKSection : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SQTKGroup X → ∀ (H : Subgroup X) (G : Type) [Group G] [Finite G]
    (π : ↥H →* G), Function.Surjective π → ∀ (L : Subgroup G) [L.Normal], CFSG.layer ↥L = ⊤ →
      IsPGroup 2 (G ⧸ L) → SQTKGroup G

@[expose] def AsA36NoOddCover : Prop :=
  ∀ (L H : Type) [Group L] [Group H] [Finite L], CFSG.IsQuasisimple L → SQTKGroup L →
    ∀ f : L →* H, Function.Surjective f → (∀ x ∈ f.ker, Odd (orderOf x)) → IsL345Type H →
      Function.Injective f

@[expose] def B51Part1Below (N : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V < N → (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → B51Part1 G L

@[expose] def AsB51NonirrSL3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → commV L ∉ IrrPlus L ⊤ →
      (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥L ≃* ↥(StatedSL 3 K))) →
      B51Case1ii G L

@[expose] def AsB51NonirrLn : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → commV L ∉ IrrPlus L ⊤ →
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧ Nonempty (↥L ≃* ↥(StatedSL 4 K))) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
          Nonempty (↥L ≃* ↥(StatedSL 5 K)))) →
      (∃ n, B51Case1iii G L n) ∨ B51Case1iv G L

end CFSG.Quasithin
