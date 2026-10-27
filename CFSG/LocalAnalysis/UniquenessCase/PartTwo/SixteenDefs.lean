module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.Quasithin.Background.F918P0
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Shapes

@[expose] def IsCyclicOrd (X : Type) [Group X] (n : ℕ) : Prop :=
  IsCyclic X ∧ Nat.card X = n

@[expose] def IsSLn (X : Type) [Group X] (n a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧ Nonempty (X ≃* ↥(StatedSL n K))

@[expose] def IsLn (X : Type) [Group X] (n a : ℕ) : Prop :=
  CFSG.Blueprint.LieModel X .PSL n 2 a

@[expose] def IsSpn (X : Type) [Group X] (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    Nonempty (X ≃* ↥(StatedSp (n / 2) K))

@[expose] def IsOmegaPlus (X : Type) [Group X] (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadPlus (n / 2) K)))

@[expose] def IsOmegaMinus (X : Type) [Group X] (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ^ a ∧
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
    Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c)))

@[expose] def IsSUn (X : Type) [Group X] (n a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ a) ^ 2 ∧
    Nonempty (X ≃* ↥(StatedSU n (2 ^ a) K))

end Shapes

section Natural

variable {W : Type} [CommGroup W]

@[expose] def NatSpn (H : Subgroup (MulAut W)) (U Z : Subgroup W) (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.nat (StatedSp (n / 2) K)).Realizes H U Z

@[expose] def NatOmegaPlus (H : Subgroup (MulAut W)) (U Z : Subgroup W) (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K))).Realizes H U Z

@[expose] def NatOmegaMinus (H : Subgroup (MulAut W)) (U Z : Subgroup W) (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ^ a ∧
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
    (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c))).Realizes H U Z

@[expose] def NatSUn (H : Subgroup (MulAut W)) (U Z : Subgroup W) (n a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ a) ^ 2 ∧
    (FFModel.nat (StatedSU n (2 ^ a) K)).Realizes H U Z

@[expose] def NatTensor (H : Subgroup (MulAut W)) (U Z : Subgroup W) (d a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.tensorNat d K).Realizes H U Z

@[expose] def SumOfNat (N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop)
    (H : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ) : Prop :=
  ∃ I : Fin k → Subgroup W, (∀ i, Z ≤ I i) ∧
    (∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ Z) ∧
    (Z ⊔ ⨆ i, I i) = U ∧ ∀ i, N H (I i) Z

@[expose] def InducesTransvection (t : MulAut W) (U : Subgroup W) : Prop :=
  t ∈ stabSub U ∧ rk ↥(commSub U (Subgroup.zpowers t)) = 1

end Natural


section Notation

variable {G : Type} [Group G]

@[expose] noncomputable def lBar (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  barSub V₀ V hV L

@[expose] noncomputable def lStar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Subgroup (MulAut (vStar M V₀ V hV L)) :=
  barSub (v1Sub M V₀ V hV L) V hV L

@[expose] def conjSet {A : Type*} [Group A] (K N : Subgroup A) : Set (Subgroup A) :=
  {X | ∃ n ∈ N, X = K.map (MulAut.conj n).toMonoidHom}

@[expose] def IsDirectProdOfConj {A : Type*} [Group A] (X K N : Subgroup A) : Prop :=
  (∀ Y ∈ conjSet K N, Y ≤ X) ∧ (⨆ Y ∈ conjSet K N, Y) = X ∧
    (∀ Y ∈ conjSet K N, ∀ Z ∈ conjSet K N, Y ≠ Z → ⁅Y, Z⁆ = ⊥) ∧
    ∀ Y ∈ conjSet K N, Y ⊓ (⨆ Z ∈ conjSet K N, ⨆ (_ : Z ≠ Y), Z) = ⊥

end Notation

section Lists

variable {G : Type} [Group G] [Finite G]
variable (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)

@[expose] noncomputable def Case153_1 : Prop :=
  IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
    NatOmegaMinus (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 6 1 ∧
    D.sig = {3} ∧ CFSG.Open.pRank 3 D.M = 3 ∧ s15 D.M V₀ V hV L = 1 ∧ mSub V₀ ≤ 2

@[expose] noncomputable def Case153_2 : Prop :=
  ∃ (K₀ : Subgroup G) (p : ℕ), K₀ ≤ L ∧
    ((p = 5 ∧ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5 ∧
        AlternatingNatural (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
          (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 5) ∨
      (p = 7 ∧ IsL3 ↥(barSub V₀ V hV K₀) 1 ∧
        BinaryNaturalSL (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
          (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ⊥ 3 1)) ∧
    IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)) ∧
    D.sig = {p} ∧ CFSG.Open.pRank p D.M = 3 ∧
    (conjSet (barSub V₀ V hV K₀)
        (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard *
      s15 D.M V₀ V hV L ≤ 2 ∧
    ((conjSet (barSub V₀ V hV K₀)
        (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard *
      s15 D.M V₀ V hV L = 1 → 2 < mSub V₀)

@[expose] noncomputable def Case153_3 : Prop :=
  (∃ K₀ : Subgroup G, K₀ ≤ L ∧ IsCyclicOrd ↥(barSub V₀ V hV K₀) 3 ∧
      IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV K₀)
        (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _)) ∧
      AlternatingNatural (barSub V₀ V hV K₀) (commSub ⊤ (barSub V₀ V hV K₀)) ⊥ 3) ∧
    (mSub V₀ ≤ 2 ∨ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 2)

@[expose] noncomputable def Desc153 : Prop :=
  Case153_1 D V₀ V hV L ∨ Case153_2 D V₀ V hV L ∨ Case153_3 D V₀ V hV L


@[expose] noncomputable def Case162_1 : Prop :=
  ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) ∨
      (IsL3 ↥(lBar V₀ V hV L) 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2)) ∧
    2 ≤ s15 D.M V₀ V hV L

@[expose] noncomputable def Case162_2 : Prop :=
  s15 D.M V₀ V hV L = 1 ∧
    ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 11 ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) ∨
      (∃ m : ℕ, 3 ≤ m ∧ m ≤ 5 ∧ IsLn ↥(lBar V₀ V hV L) m 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) ∨
      (IsSpn ↥(lBar V₀ V hV L) 6 1 ∧
        SumOfNat (fun H U Z => NatSpn H U Z 6 1)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) 8 1 ∧
        SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2))

@[expose] noncomputable def Case162_3 : Prop :=
  IsCyclicOrd ↥(lBar V₀ V hV L) 5 ∧ rk ↥(wTil V₀ V hV L) = 4 ∧ 2 ≤ s15 D.M V₀ V hV L

@[expose] noncomputable def Case162_4 : Prop :=
  IsPOnePlusTwo 3 ↥(lBar V₀ V hV L) ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ 1 ≤ s15 D.M V₀ V hV L

@[expose] noncomputable def Case162_5 : Prop :=
  (∃ r : ℕ, IsElemAbelianOfRank 3 r ↥(lBar V₀ V hV L) ∧ rk ↥(wTil V₀ V hV L) = 2 * (r + 1)) ∧
    1 ≤ s15 D.M V₀ V hV L

@[expose] noncomputable def Case162_6 : Prop :=
  IsSUn ↥(lBar V₀ V hV L) 4 1 ∧ NatSUn (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 4 1 ∧
    s15 D.M V₀ V hV L = 1 ∧ D.sig = {3} ∧ CFSG.Open.pRank 3 D.M = 3

@[expose] noncomputable def Case162_7 : Prop :=
  IsOmegaPlus ↥(lBar V₀ V hV L) 4 2 ∧
    NatOmegaPlus (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 4 2 ∧ s15 D.M V₀ V hV L = 1

@[expose] noncomputable def Case162_8 : Prop :=
  ((UC22.IsL2 ↥(lBar V₀ V hV L) 2 ∧
        BinaryNaturalSL (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2 2) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) 4 2 ∧
        NatOmegaMinus (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 4 2)) ∧
    2 ≤ s15 D.M V₀ V hV L

@[expose] noncomputable def Case162_9 : Prop :=
  IsSpn ↥(lBar V₀ V hV L) 6 1 ∧ gamma15 D.M V₀ V hV L = 8 ∧ s15 D.M V₀ V hV L = 1 ∧
    D.sig = {3} ∧ CFSG.Open.pRank 3 D.M = 3

@[expose] noncomputable def Concl162 : Prop :=
  Desc153 D V₀ V hV L ∨ Case162_1 D V₀ V hV L ∨ Case162_2 D V₀ V hV L ∨ Case162_3 D V₀ V hV L ∨
    Case162_4 D V₀ V hV L ∨ Case162_5 D V₀ V hV L ∨ Case162_6 D V₀ V hV L ∨
    Case162_7 D V₀ V hV L ∨ Case162_8 D V₀ V hV L ∨ Case162_9 D V₀ V hV L


@[expose] noncomputable def Case163_1 : Prop :=
  IsL3 ↥(lBar V₀ V hV L) 1 ∧ gamma15 D.M V₀ V hV L = 8 ∧ s15 D.M V₀ V hV L = 2

@[expose] noncomputable def Case163_2 : Prop :=
  IsOmegaPlus ↥(lBar V₀ V hV L) 4 3 ∧ NatOmegaPlus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 4 3 ∧
    s15 D.M V₀ V hV L = 1

@[expose] noncomputable def Case163_3 : Prop :=
  IsOmegaMinus ↥(lBar V₀ V hV L) 4 3 ∧ NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 4 3 ∧
    s15 D.M V₀ V hV L = 2 ∧ D.sig ⊆ {5, 13}

@[expose] noncomputable def Case163_4 : Prop :=
  UC22.IsL2 ↥(lBar V₀ V hV L) 3 ∧
    BinaryNaturalSL (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2 3 ∧
    (s15 D.M V₀ V hV L = 2 ∨ s15 D.M V₀ V hV L = 3)

@[expose] noncomputable def Case163_5 : Prop :=
  ((IsL3 ↥(lBar V₀ V hV L) 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 3) ∨
      (UC22.IsAlt ↥(lBar V₀ V hV L) 5 ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
          (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 3)) ∧
    s15 D.M V₀ V hV L = 2

@[expose] noncomputable def Case163_6 : Prop :=
  IsOmegaMinus ↥(lBar V₀ V hV L) 6 3 ∧ NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 3 ∧
    s15 D.M V₀ V hV L = 1 ∧ D.sig = {3} ∧ CFSG.Open.pRank 3 D.M = 3

@[expose] noncomputable def Case163_7 : Prop :=
  Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L))) ∧
    IsL3 ↥(lBar V₀ V hV L) 1 ∧
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 3 ∧ D.sig = {7}

@[expose] noncomputable def Case163_8 : Prop :=
  (∃ (X : Type) (_ : Group X), IsL3 X 1 ∧ Nonempty (↥(lBar V₀ V hV L) ≃* (X × X))) ∧
    NatTensor (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 1 ∧ s15 D.M V₀ V hV L = 1 ∧ D.sig = {7}

@[expose] noncomputable def Case163_9 : Prop :=
  IsCyclicOrd ↥(lBar V₀ V hV L) 3 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ 2 ≤ s15 D.M V₀ V hV L

@[expose] noncomputable def Case163_10 : Prop :=
  IsElemAbelianOfRank 3 2 ↥(lBar V₀ V hV L) ∧ rk ↥(wTil V₀ V hV L) = 8

@[expose] noncomputable def Case163_11 : Prop :=
  ∃ r : ℕ, IsElemAbelianOfRank 7 r ↥(lBar V₀ V hV L) ∧ rk ↥(wTil V₀ V hV L) = 3 * (r + 1)

@[expose] noncomputable def Case163_12 : Prop :=
  IsCyclicOrd ↥(lBar V₀ V hV L) 7 ∧ rk ↥(wTil V₀ V hV L) = 3 ∧ 1 < s15 D.M V₀ V hV L

@[expose] noncomputable def Concl163 : Prop :=
  Concl162 D V₀ V hV L ∨ Case163_1 D V₀ V hV L ∨ Case163_2 D V₀ V hV L ∨ Case163_3 D V₀ V hV L ∨
    Case163_4 D V₀ V hV L ∨ Case163_5 D V₀ V hV L ∨ Case163_6 D V₀ V hV L ∨
    Case163_7 D V₀ V hV L ∨ Case163_8 D V₀ V hV L ∨ Case163_9 D V₀ V hV L ∨
    Case163_10 V₀ V hV L ∨ Case163_11 V₀ V hV L ∨ Case163_12 D V₀ V hV L

@[expose] noncomputable def Case164_2 : Prop :=
  ((UC22.IsAlt ↥(lBar V₀ V hV L) 5 ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
          (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 2) ∨
      (IsL3 ↥(lBar V₀ V hV L) 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
          (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 2)) ∧
    D.sig = {3} ∧ CFSG.Open.pRank 3 D.M = 3 ∧
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)))

@[expose] noncomputable def Case164_3 : Prop :=
  IsL3 ↥(lBar V₀ V hV L) 1 ∧
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 ∧
    D.sig = {7} ∧ CFSG.Open.pRank 7 D.M = 3 ∧
    Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)))

@[expose] noncomputable def Case164_4 : Prop :=
  ∃ p : ℕ, (p = 3 ∨ p = 7) ∧ IsCyclicOrd ↥(lBar V₀ V hV L) p ∧
    rk ↥(wTil V₀ V hV L) = 2 * dParam p ∧ D.sig = {p} ∧ CFSG.Open.pRank p D.M = 3 ∧
    IsElemAbelianOfRank p 3 ↥(fstarBar D.M V₀ V hV)

@[expose] noncomputable def Concl164 : Prop :=
  s15 D.M V₀ V hV L = 2 ∧
    (gamma15 D.M V₀ V hV L ≤ 3 ∨ Case164_2 D V₀ V hV L ∨ Case164_3 D V₀ V hV L ∨
      Case164_4 D V₀ V hV L)

@[expose] noncomputable def Case167_1 : Prop :=
  IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
    NatOmegaMinus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 6 1 ∧ D.sig = {3} ∧
      CFSG.Open.pRank 3 D.M = 3

@[expose] noncomputable def Case167_2 : Prop :=
  IsL3 ↥(lBar V₀ V hV L) 1 ∧
    BinaryNaturalSL (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 3 1 ∧
    s15 D.M V₀ V hV L = 2 ∧ D.sig = {7}

@[expose] noncomputable def Case167_3 : Prop :=
  IsCyclicOrd ↥(lBar V₀ V hV L) 3 ∧ rk ↥(wTil V₀ V hV L) = 2 ∧ s15 D.M V₀ V hV L = 2 ∧
    D.sig = {3}

@[expose] noncomputable def Case167_4 : Prop :=
  IsSUn ↥(lBar V₀ V hV L) 4 1 ∧
    NatSUn (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 4 1 ∧ D.sig = {3}

@[expose] noncomputable def Case167_5 : Prop :=
  IsOmegaPlus ↥(lBar V₀ V hV L) 4 2 ∧
    NatOmegaPlus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 4 2 ∧ D.sig = {5}

@[expose] noncomputable def Case167_6 : Prop :=
  IsOmegaPlus ↥(lBar V₀ V hV L) 4 3 ∧
    NatOmegaPlus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 4 3 ∧ D.sig = {3}

@[expose] noncomputable def Case167_7 : Prop :=
  (∃ (X : Type) (_ : Group X), IsL3 X 1 ∧ Nonempty (↥(lBar V₀ V hV L) ≃* (X × X))) ∧
    NatTensor (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 3 1 ∧ D.sig = {7}

@[expose] noncomputable def Case167_8 : Prop :=
  IsSpn ↥(lBar V₀ V hV L) 6 1 ∧ rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) = 8 ∧ D.sig = {3} ∧
    CFSG.Open.pRank 3 D.M = 3

@[expose] noncomputable def Concl167 : Prop :=
  Case167_1 D V₀ V hV L ∨ Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L ∨
    Case167_4 D V₀ V hV L ∨ Case167_5 D V₀ V hV L ∨ Case167_6 D V₀ V hV L ∨
    Case167_7 D V₀ V hV L ∨ Case167_8 D V₀ V hV L

end Lists

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
