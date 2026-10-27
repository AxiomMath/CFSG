module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Natural

variable {W : Type} [CommGroup W]

@[expose] def NatOrthPlus (H : Subgroup (MulAut W)) (U Z : Subgroup W) (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.nat (CFSG.MatrixModel.isometryCore (StatedQuadPlus (n / 2) K))).Realizes H U Z

@[expose] def NatOrthMinus (H : Subgroup (MulAut W)) (U Z : Subgroup W) (n a : ℕ) : Prop :=
  Even n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K), Nat.card K = 2 ^ a ∧
    (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
    (FFModel.nat (CFSG.MatrixModel.isometryCore (StatedQuadMinus (n / 2) K b c))).Realizes H U Z

@[expose] def GenByTransvections (J : Subgroup (MulAut W)) (R : Subgroup W) : Prop :=
  J = Subgroup.closure {t : MulAut W | t ∈ J ∧ InducesTransvection t R}

@[expose] def s15JNat (J : Subgroup (MulAut W)) (R : Subgroup W) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ BinaryNaturalSL J R ⊥ n 1) ∨
  (∃ n : ℕ, 4 ≤ n ∧ NatSpn J R ⊥ n 1) ∨
  (∃ n : ℕ, 6 ≤ n ∧ NatOrthPlus J R ⊥ n 1) ∨
  (∃ n : ℕ, 4 ≤ n ∧ NatOrthMinus J R ⊥ n 1) ∨
  (∃ m : ℕ, 3 ≤ m ∧ SymmetricNatural J R ⊥ m)

@[expose] def s15SecIso (X : Subgroup (MulAut W)) (I N I' N' : Subgroup W) : Prop :=
  ∃ β : ↥I →* ↥I' ⧸ N'.subgroupOf I',
    Function.Surjective β ∧ (∀ u : ↥I, β u = 1 ↔ (u : W) ∈ N) ∧
    ∀ x ∈ X, ∀ (u : ↥I) (u' : ↥I') (hu : x (u : W) ∈ I) (hu' : x (u' : W) ∈ I'),
      β u = QuotientGroup.mk u' → β ⟨x (u : W), hu⟩ = QuotientGroup.mk ⟨x (u' : W), hu'⟩

end Natural

section KTypes

variable {V : Type} [CommGroup V]

@[expose] def s15KNatPerf (X : Type) [Group X] (K : Subgroup (MulAut V)) (Z : Subgroup V) : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ IsLn X n 1 ∧ BinaryNaturalSL K Z ⊥ n 1) ∨
  (∃ n : ℕ, 6 ≤ n ∧ IsSpn X n 1 ∧ NatSpn K Z ⊥ n 1) ∨
  (∃ n : ℕ, 6 ≤ n ∧ IsOmegaPlus X n 1 ∧ NatOmegaPlus K Z ⊥ n 1) ∨
  (∃ n : ℕ, 6 ≤ n ∧ IsOmegaMinus X n 1 ∧ NatOmegaMinus K Z ⊥ n 1) ∨
  (∃ n : ℕ, 5 ≤ n ∧ UC22.IsAlt X n ∧ AlternatingNatural K Z ⊥ n)

@[expose] def s15KNatZ3 (X : Type) [Group X] (K : Subgroup (MulAut V)) (Z : Subgroup V) : Prop :=
  IsCyclicOrd X 3 ∧ AlternatingNatural K Z ⊥ 3

@[expose] def s15KNat (X : Type) [Group X] (K : Subgroup (MulAut V)) (Z : Subgroup V) : Prop :=
  s15KNatPerf X K Z ∨ s15KNatZ3 X K Z

@[expose] def s15ExcList (X : Type) [Group X] : Prop :=
  IsL3 X 1 ∨ IsLn X 4 1 ∨ UC22.IsAlt X 5 ∨ UC22.IsAlt X 6 ∨ UC22.IsAlt X 7 ∨ IsOmegaMinus X 6 1

@[expose] def s15ListTwo (X : Type) [Group X] : Prop :=
  IsL3 X 1 ∨ UC22.IsAlt X 5

@[expose] def s15ListFour (X : Type) [Group X] : Prop :=
  IsOmegaMinus X 6 1 ∨ UC22.IsAlt X 6 ∨ UC22.IsAlt X 7 ∨ IsLn X 4 1

theorem s15ExcList_iff (X : Type) [Group X] : s15ExcList X ↔ s15ListTwo X ∨ s15ListFour X := by
  unfold s15ExcList s15ListTwo s15ListFour
  tauto

end KTypes

@[expose] def RMcLaughlin : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (J : Subgroup (MulAut W)) (R : Subgroup W), J ≠ ⊥ → IsIrrOn J R ⊥ →
      (∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) → GenByTransvections J R → s15JNat J R

@[expose] def RNormNat153 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (J : Subgroup (MulAut W)) (R : Subgroup W), s15JNat J R → StableUnder J R →
      (∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) →
      ∀ x ∈ stabSub R, (∀ j : MulAut W, j ∈ J ↔ x * j * x⁻¹ ∈ J) →
        ∃ j ∈ J, ∀ r ∈ R, x r = j r

@[expose] def RTable137 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut V)) (Z : Subgroup V) (X : Type) [Group X], s15KNatPerf X K Z →
      (∀ z ∈ Z, 1 ≤ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z)) ∧
      ((∃ z ∈ Z, z ≠ 1 ∧ CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z) ≤ 1) →
        s15ExcList X)

@[expose] def RIso153 : Prop :=
  ∀ (X : Type) [Group X], IsLn X 4 1 ↔ UC22.IsAlt X 8

@[expose] def RSchur153 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    (UC22.IsAlt (X ⧸ Subgroup.center X) 6 → UC22.IsAlt X 6 ∨ F08.IsA6Z3 X) ∧
    (UC22.IsAlt (X ⧸ Subgroup.center X) 7 → UC22.IsAlt X 7 ∨ F08.IsA7Z3 X) ∧
    (UC22.IsAlt (X ⧸ Subgroup.center X) 8 → UC22.IsAlt X 8) ∧
    (IsLn (X ⧸ Subgroup.center X) 5 1 → IsLn X 5 1)

@[expose] def RNotJ2 : Prop :=
  ∀ (X : Type) [Group X], IsSpor X .J2 →
    ¬ (UC22.IsAlt X 6 ∨ F08.IsA6Z3 X ∨ UC22.IsAlt X 7 ∨ F08.IsA7Z3 X ∨ UC22.IsAlt X 8 ∨
        IsLn X 5 1)

@[expose] def RAutRank153 : Prop :=
  ∀ (S H : Type) [Group S] [Group H] [Finite S] [Finite H] (f : S →* H), Function.Injective f →
    f.range.Normal → (∀ h : H, (∀ s : S, h * f s = f s * h) → h = 1) →
      (s15ListTwo S →
        (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 1) ∧
        (IsL3 S 1 → ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 ∨ p = 7) ∧
        (UC22.IsAlt S 5 → ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 ∨ p = 5)) ∧
      (s15ListFour S →
        (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 1) ∧
        CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3 ∧
        (¬ IsOmegaMinus S 6 1 → CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2))

@[expose] def RRank3List153 : Prop :=
  ∀ (V : Type) [CommGroup V] (X : Type) [Group X] [Finite X]
    (K : Subgroup (MulAut V)) (Z : Subgroup V),
    s15KNatPerf X K Z →
      (CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 →
        IsLn X 3 1 ∨ IsLn X 4 1 ∨ IsLn X 5 1 ∨ UC22.IsAlt X 5 ∨ UC22.IsAlt X 6 ∨
          UC22.IsAlt X 7 ∨ UC22.IsAlt X 8) ∧
      (CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 → IsL3 X 1 ∨ UC22.IsAlt X 5)

@[expose] def RPerfType153 : Prop :=
  ∀ (V : Type) [CommGroup V] (X : Type) [Group X] (K : Subgroup (MulAut V)) (Z : Subgroup V),
    s15KNatPerf X K Z →
      (IsL3 X 1 → BinaryNaturalSL K Z ⊥ 3 1) ∧
      (UC22.IsAlt X 5 → AlternatingNatural K Z ⊥ 5) ∧
      (UC22.IsAlt X 6 → AlternatingNatural K Z ⊥ 6) ∧
      (UC22.IsAlt X 7 → AlternatingNatural K Z ⊥ 7) ∧
      (IsOmegaMinus X 6 1 → NatOmegaMinus K Z ⊥ 6 1)

@[expose] def R1111_153 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, F11.Hyp11 D V₀ V →
    ∀ [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal],
    ∀ p ∈ D.sig, CFSG.Open.pRank p D.M - 2 ≤
        CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) ∧
      1 ≤ CFSG.Open.pRank p D.M - 2

@[expose] def RAbsIrr153 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Type) [Group X] (K : Subgroup (MulAut V)) (Z : Subgroup V), s15KNatPerf X K Z →
      ∀ x ∈ stabSub Z, (∀ k ∈ K, x * k = k * x) → ∀ z ∈ Z, x z = z

section Notation

variable (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L K₀ : Subgroup G)

@[expose] noncomputable def s15NBar : Subgroup (MulAut (Vtil V₀ V hV)) :=
  Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _)

@[expose] noncomputable def s15Rs : ℕ :=
  (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard * s15 D.M V₀ V hV L

@[expose] def s15O1a : Prop :=
  ∀ v ∈ V, v ≠ 1 → 1 < CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G))

@[expose] noncomputable def s15Shape : Prop :=
  K₀ ≤ L ∧ barSub V₀ V hV K₀ ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ ∧
    IsDirectProdOfConj (lBar V₀ V hV L) (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L) ∧
    s15KNat ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) ∧
    sSupIndep {Z : Subgroup (vStar D.M V₀ V hV L) | ∃ m ∈ D.M,
      Z = commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m))} ∧
    sSup {Z : Subgroup (vStar D.M V₀ V hV L) | ∃ m ∈ D.M,
      Z = commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m))} = ⊤

@[expose] noncomputable def s15Trich : Prop :=
  s15O1a D V ∨ IsCyclicOrd ↥(barSub V₀ V hV K₀) 3 ∨
    (s15Rs D V₀ V hV L K₀ = 1 ∧ s15ExcList ↥(lBar V₀ V hV L))

@[expose] noncomputable def s15XStar : Subgroup (MulAut (vStar D.M V₀ V hV L)) :=
  ⨆ m ∈ D.M, barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup K₀ m)

@[expose] noncomputable def s15Covers (K : Subgroup G) : Prop :=
  K ∈ calC D.M ∧ ∃ m ∈ D.M, barSub V₀ V hV K = barSub V₀ V hV (conjSubgroup K₀ m) ∧
    Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥(barSub V₀ V hV K₀))

end Notation

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
