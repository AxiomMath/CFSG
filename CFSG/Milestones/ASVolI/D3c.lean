module

public import CFSG.Milestones.ASVolI.D3b

public section

namespace CFSG.ASVolI.ChD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

structure CtxD310 [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  std : D3Std M Mp T L V
  Mp_eq : Mp = L
  qhatM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ)
  not_one : ¬ ((∀ t ∈ T, t ∈ stabSub V) ∧ V = orbSup T V)
  not_two : ¬ D310TwoIn T L V ⊤

@[expose] def IsHomLift (L : Subgroup (MulAut W)) (V U : Subgroup W) : Prop :=
  modFix L ⊤ ≤ U ∧ IsHomogComp L ⊤ (tilde L ⊤ U) ∧ tilde L ⊤ V ≤ tilde L ⊤ U

@[expose] def IsD39X (M L A X : Subgroup (MulAut W)) : Prop :=
  X ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) ∧ (∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) ∧
    X = cmt X (A ⊓ Subgroup.centralizer (L : Set (MulAut W))) ∧
    ((∃ K : Subgroup (MulAut W), IsCompOf K M ∧ ¬ IsSuzukiGp K ∧ X = conjClosure K A) ∨
      (X ≤ pCoreOf 3 M ∧ Nat.card ↥X = 3))

end CFSG.ASVolI.ChD

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChD

@[expose] def D_3_11 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → D310TwoIn T L V (orbSup T V)

section


theorem as_D_3_11
    : D_3_11 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_12 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → ∀ A ∈ QhatStar T, ∀ U : Subgroup W, IsHomLift L V U → A ≤ stabSub U

section


theorem as_D_3_12
    : D_3_12 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_13 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → ∀ A ∈ QhatStar T, ¬ (∀ a ∈ A, (∀ x ∈ L, a * x = x * a) → a = 1)

section


theorem as_D_3_13
    : D_3_13 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_14 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V →
      CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) = 1 ∧
        ∃ m : ℕ, Odd m ∧ IsPSL 3 2 m ↥L

section


theorem as_D_3_14
    : D_3_14 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_15 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → ∀ A ∈ QhatStar T, ∀ X : Subgroup (MulAut W), IsD39X M L A X →
      X = cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A ∧
      ((X = pCoreOf 3 M ∧ Nat.card ↥X = 3) ∨
        (IsCompOf X M ∧ M ≤ Subgroup.normalizer (X : Set (MulAut W))))

section


theorem as_D_3_15
    : D_3_15 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_16 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → fixV L = ⊥ ∧ V ⊓ fixV M = ⊥

section


theorem as_D_3_16
    : D_3_16 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_17 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → ∀ A ∈ QhatStar T, ∀ U : Subgroup W, IsHomLift L V U →
      (∃ n : ℕ, Odd n ∧
        IsPSL 3 2 n ↥(cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A)) ∧
      ((∃ I : Subgroup W, I ∈ IrrPlusOn (cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A)
          U (T ⊓ stabSub U)) ∧
        ∀ I : Subgroup W, I ∈ IrrPlusOn (cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A)
            U (T ⊓ stabSub U) →
          ∃ n : ℕ, BinaryNaturalSL (cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A) I ⊥ 3 n) ∧
      (∀ a ∈ A, ∃ x ∈ cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A,
        ∀ y ∈ cmt (fstarSub (M ⊓ Subgroup.centralizer (L : Set (MulAut W)))) A,
          a * y * a⁻¹ = x * y * x⁻¹)

section


theorem as_D_3_17
    : D_3_17 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_18 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → ∀ A ∈ QhatStar T, L = cmt L A

section


theorem as_D_3_18
    : D_3_18 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

@[expose] def D_3_19 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    CtxD310 M Mp T L V → ∀ A ∈ QhatStar T,
      rAV (autSub A (orbSup T V)) =
        ((mRel (orbSup T V) (orbSup T V ⊓ fixV A) : ℕ) : ℚ) /
          ((mRel A (A ⊓ Subgroup.centralizer (L : Set (MulAut W))) : ℕ) : ℚ) ∧
      rAV (autSub A (orbSup T V)) < 2

section


theorem as_D_3_19
    : D_3_19 := by
  intro W _ _ M Mp T L V h
  rcases as_D_3_10 W M Mp T L V h.std h.Mp_eq h.qhatM with h1 | h2
  · exact (h.not_one h1).elim
  · exact (h.not_two h2).elim

end

end CFSG.ASVolI
