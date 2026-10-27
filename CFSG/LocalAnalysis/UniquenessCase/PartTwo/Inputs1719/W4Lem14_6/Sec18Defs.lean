module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs
public import CFSG.Quasithin.Background.IrredInvolutionRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def Sec18Shape {W : Type} [CommGroup W] (Y L X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  ((IsL2 ↥L n ∨ IsSz ↥L n) ∧ 2 < n ∧
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y).ncard ≤ 2) ∨
    (X = L ∧ n = 2 ∧ LieModel ↥X .PSU 5 2 2) ∨
    (X = L ∧ Odd n ∧ 1 < n ∧ (IsSp4 ↥X n ∨ IsG2 ↥X n)) ∨
    (X = L ∧ 1 < n ∧ IsU4 ↥X n)

@[expose] def Sec18Concl {W : Type} [CommGroup W] (Y L X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  (IsSp4 ↥X n ∧ NatSpn X ⊤ (fixV X) 4 n) ∨
    (IsG2 ↥X n ∧ G2Natural X ⊤ (fixV X) n) ∨
    (IsSUn ↥X 4 n ∧ NatSUn X ⊤ (fixV X) 4 n) ∨
    (IsOmegaMinus ↥X 6 n ∧ NatOmegaMinus X ⊤ (fixV X) 6 n) ∨
    (IsOmegaPlus ↥X 4 n ∧ NatOmegaPlus X ⊤ (fixV X) 4 n) ∨
    (Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧ NatOmegaMinus X ⊤ (fixV X) 4 (n / 2)) ∨
    (IsL2 ↥X n ∧ BinaryNaturalSL X ⊤ (fixV X) 2 n) ∨
    ((IsSp4 ↥X n ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSp 2 K) →* ↥X),
          Nat.card K = 2 ^ n ∧
            SumOfNatVia (FFModel.nat (StatedSp 2 K)) X ⊤ ⊥ 2 π) ∨
      (IsOmegaMinus ↥X 6 n ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
          (π : ↥(StatedOmega (StatedQuadMinus 3 K b c)) →* ↥X),
          Nat.card K = 2 ^ n ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
            SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))) X ⊤ ⊥ 2 π) ∨
      (Even n ∧ IsOmegaMinus ↥X 4 (n / 2) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
          (π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →* ↥X),
          Nat.card K = 2 ^ (n / 2) ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
            SumOfNatVia (FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c))) X ⊤ ⊥ 2 π) ∨
      (n = 2 ∧ IsSUn ↥X 4 n ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSU 4 (2 ^ n) K) →* ↥X),
          Nat.card K = (2 ^ n) ^ 2 ∧
            SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ n) K)) X ⊤ ⊥ 2 π)) ∨
    ((IsOmegaMinus ↥X 6 2 ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2) X ⊤ ⊥ 3) ∨
      (IsOmegaMinus ↥X 4 2 ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2) X ⊤ ⊥ 3)) ∨
    (X ≠ L ∧ ∀ g : MulAut W, g ∈ Y → g ∉ normIn Y L →
      commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥) ∨
    (IsL3 ↥X 1 ∧
      (∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥X,
        SumOfNatVia (FFModel.nat (StatedSL 3 (ZMod 2))) X ⊤ ⊥ 4 π) ∧
      IsSubgroupOfAlt ↥(centGroupIn Y L) 8 ∧
      (7 ∣ Nat.card (centGroupIn Y L) →
        IsAlt ↥(centGroupIn Y L) 8 ∨ IsAlt ↥(centGroupIn Y L) 7 ∨
          IsL3 ↥(centGroupIn Y L) 1)) ∨
    (Fstar Y = X ∧ LieModel ↥X .PSL 3 2 2 ∧
      (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 9)) ∨
    ((Fstar Y = X ∧
        ((IsL2 ↥X 3 ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 8)) ∨
          (IsL2 ↥X 4 ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16)) ∨
          (IsL2 ↥X 6 ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16)))) ∨
      (IsZ3xL2_64 ↥(Fstar Y) ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16)))

theorem w4Lem14_6Sec18_of_concl
    (h : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (Y L X : Subgroup (MulAut W)) (n : ℕ),
        CFSG.IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y → IsComponentOf L Y →
        X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom → Sec18Shape Y L X n →
        3 < E3.mParam Y → E3.mParam Y ≤ max (bParam X Y) n + 2 →
        (fixV X = ⊥ ∨ commPset Y X = X) → Sec18Concl Y L X n) :
    W4Lem14_6Sec18 := by
  intro W _ _ hW Y L X n hK hO2 hB hL hX hcase hm hle hfix
  exact h W hW Y L X n hK hO2 hB hL hX hcase hm hle hfix

@[expose] def K146FFL2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ), O2Trivial Y → IsComponentOf L Y →
      IsL2 ↥L n → 2 < n → (∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) →
      IsIrrOn L (commV L) (commV L ⊓ fixV L) ∧
        BinaryNaturalSL L (commV L) (commV L ⊓ fixV L) 2 n

@[expose] def K146FFSz : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ), O2Trivial Y → IsComponentOf L Y →
      IsSz ↥L n → ∀ A ∈ Pset Y, ⁅A, L⁆ = ⊥

@[expose] def K146FFU54 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)), O2Trivial Y → IsComponentOf L Y →
      LieModel ↥L .PSU 5 2 2 → ∀ A ∈ Pset Y, ⁅A, L⁆ = ⊥

@[expose] def K146FFSp4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ), O2Trivial Y → IsComponentOf L Y →
      IsSp4 ↥L n → 1 < n → (∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) →
      NatSpn L (commV L) (commV L ⊓ fixV L) 4 n

@[expose] def K146FFG2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ), O2Trivial Y → IsComponentOf L Y →
      IsG2 ↥L n → 1 < n → Odd n → (∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) →
      G2Natural L (commV L) (commV L ⊓ fixV L) n

@[expose] def K146FFU4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ), O2Trivial Y → IsComponentOf L Y →
      IsU4 ↥L n → 1 < n → (∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) →
      (IsSUn ↥L 4 n ∧ NatSUn L (commV L) (commV L ⊓ fixV L) 4 n) ∨
        (IsOmegaMinus ↥L 6 n ∧ NatOmegaMinus L (commV L) (commV L ⊓ fixV L) 6 n)

@[expose] def W4Lem4_17Sp4G2N : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W), ∀ n : ℕ,
      L ≤ Y → T ≤ Y → L ⊔ T = Y →
      IsComponentOf L Y →
      IsSylowIn 2 T Y →
      fixV T ≠ fixV Y →
      Odd (Nat.card (Subgroup.center ↥L)) →
      T ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      1 < n → (IsSp4 ↥L n ∨ IsG2 ↥L n) →
      bParam L Y ≤ 2 * n

@[expose] def W4Lem4_17U4U5N : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L T : Subgroup (MulAut W), ∀ n : ℕ,
      L ≤ Y → T ≤ Y → L ⊔ T = Y →
      IsComponentOf L Y →
      IsSylowIn 2 T Y →
      fixV T ≠ fixV Y →
      Odd (Nat.card (Subgroup.center ↥L)) →
      T ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      1 < n → (IsU4 ↥L n ∨ IsU5 ↥L n) →
      bParam L Y ≤ 3 * n

@[expose] def K146ModL2 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsL2 ↥S n → 2 < n → IsIrrOn S ⊤ ⊥ → E3.mParam N ≤ n + 2 →
      (BinaryNaturalSL S ⊤ ⊥ 2 n ∧ n ≤ E3.mParam N) ∨
        (Even n ∧ NatOmegaMinus S ⊤ ⊥ 4 (n / 2) ∧ n ≤ 2 * E3.mParam N) ∨
        (n = 3 ∧ rk U = 8 ∧ 4 ≤ E3.mParam N ∧
          Subgroup.centralizer (S : Set (MulAut U)) = ⊥) ∨
        (n = 4 ∧ rk U = 16 ∧ 6 ≤ E3.mParam N ∧
          Subgroup.centralizer (S : Set (MulAut U)) = ⊥) ∨
        (n = 6 ∧ rk U = 16 ∧ 8 ≤ E3.mParam N ∧
          Nat.card (Subgroup.centralizer (S : Set (MulAut U))) ∣ 3)

@[expose] def K146ModSz : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsSz ↥S n → IsIrrOn S ⊤ ⊥ → 2 * n ≤ E3.mParam N

@[expose] def K146ModSp4 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsSp4 ↥S n → Odd n → 1 < n → IsIrrOn S ⊤ ⊥ → E3.mParam N ≤ 2 * n + 2 →
      NatSpn S ⊤ ⊥ 4 n ∧ n ≤ E3.mParam N

@[expose] def K146ModG2 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsG2 ↥S n → Odd n → 1 < n → IsIrrOn S ⊤ ⊥ → E3.mParam N ≤ 2 * n + 2 →
      G2Natural S ⊤ ⊥ n ∧ 2 * n ≤ E3.mParam N

@[expose] def K146ModU4 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsU4 ↥S n → 1 < n → IsIrrOn S ⊤ ⊥ → E3.mParam N ≤ 3 * n + 2 →
      (IsSUn ↥S 4 n ∧ NatSUn S ⊤ ⊥ 4 n ∧ 2 * n ≤ E3.mParam N) ∨
        (IsOmegaMinus ↥S 6 n ∧ NatOmegaMinus S ⊤ ⊥ 6 n ∧ n ≤ E3.mParam N) ∨
        (n = 2 ∧ 3 * n + 2 < 2 * E3.mParam N ∧ E3.aParam N + 2 < E3.mParam N)

@[expose] def K146ModU54 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)), S ≤ N → (S.subgroupOf N).Normal →
      LieModel ↥S .PSU 5 2 2 → IsIrrOn S ⊤ ⊥ → 8 < E3.mParam N

@[expose] def K146Om6mA : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal → 1 < n →
      NatOmegaMinus S ⊤ ⊥ 6 n →
      E3.aParam N ≤ 2 * n + 1 ∧ (Odd n → E3.aParam N ≤ 2 * n)

@[expose] def K146Sp4TwoNat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ) (I J : Subgroup W), L ≤ Y → (L.subgroupOf Y).Normal →
      IsSp4 ↥L n → Odd n → 1 < n →
      NatSpn L I ⊥ 4 n → NatSpn L J ⊥ 4 n → I ⊓ J = ⊥ → I ⊔ J = ⊤ →
      ¬ SecIsoOn L I ⊥ J ⊥ →
      3 * n ≤ E3.mParam Y

@[expose] def K146NatIsoOm4m : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut W)) (n : ℕ) (I J : Subgroup W), IsL2 ↥L n → Even n → 2 < n →
      NatOmegaMinus L I ⊥ 4 (n / 2) → NatOmegaMinus L J ⊥ 4 (n / 2) → SecIsoOn L I ⊥ J ⊥

@[expose] def K146NatIsoU4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut W)) (n : ℕ) (I J : Subgroup W), IsU4 ↥L n → 1 < n →
      ((NatSUn L I ⊥ 4 n ∧ NatSUn L J ⊥ 4 n) ∨
        (NatOmegaMinus L I ⊥ 6 n ∧ NatOmegaMinus L J ⊥ 6 n)) →
      SecIsoOn L I ⊥ J ⊥

@[expose] def K146U54InvRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 5 2 2 → IrredInvolutionRankBound S 9

@[expose] def K146U54OuterInv : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSU 5 2 2 →
    ∀ α : MulAut S, α ^ 2 = 1 → (¬ ∃ g : S, ∀ x, α x = g * x * g⁻¹) →
      ∃ y : S, orderOf y = 41 ∧ α y = y⁻¹

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
