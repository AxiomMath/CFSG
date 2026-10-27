module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def W4Lem14_6aSmall : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L X : Subgroup (MulAut W),
      CFSG.IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y → IsComponentOf L Y →
      X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom →
      (UC22.IsL2 ↥L 3 ∨ UC22.IsSz ↥L 5) →
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y).ncard ≤ 2 →
      fixV X = ⊥ → 3 < E3.mParam Y → E3.mParam Y ≤ bParam X Y + 2 → False

@[expose] def W4Lem14_6Sec18 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L X : Subgroup (MulAut W), ∀ n : ℕ,
      IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y →
      IsComponentOf L Y →
      X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom →
      (((IsL2 ↥L n ∨ IsSz ↥L n) ∧ 2 < n ∧
          (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y).ncard ≤ 2) ∨
        (X = L ∧ n = 2 ∧ LieModel ↥X .PSU 5 2 2) ∨
        (X = L ∧ Odd n ∧ 1 < n ∧ (IsSp4 ↥X n ∨ IsG2 ↥X n)) ∨
        (X = L ∧ 1 < n ∧ IsU4 ↥X n)) →
      3 < E3.mParam Y →
      E3.mParam Y ≤ max (bParam X Y) n + 2 →
      (fixV X = ⊥ ∨ commPset Y X = X) →
      ((IsSp4 ↥X n ∧ NatSpn X ⊤ (fixV X) 4 n) ∨
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
          (IsZ3xL2_64 ↥(Fstar Y) ∧ (IsIrrOn X ⊤ ⊥ ∧ E3.mQuot (⊤ : Subgroup W) ⊥ = 16))))

@[expose] def K_L28SmallM : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ N S : Subgroup (MulAut U), S ≤ N → (S.subgroupOf N).Normal → UC22.IsL2 ↥S 3 →
      IsIrrOn S ⊤ ⊥ →
      3 ≤ E3.mParam N ∧
        (E3.mParam N ≤ 5 →
          (rk U = 6 ∧ ∃ t ∈ S, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) = 3) ∨
            (rk U = 8 ∧ E3.aParam N ≤ 1))

@[expose] def K_SzThirtyTwoMinM : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ N S : Subgroup (MulAut U), S ≤ N → (S.subgroupOf N).Normal → UC22.IsSz ↥S 5 →
      IsIrrOn S ⊤ ⊥ → 8 ≤ E3.mParam N

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
