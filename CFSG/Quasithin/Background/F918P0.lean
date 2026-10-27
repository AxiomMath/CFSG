module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

section Vocab

variable {W : Type} [CommGroup W]

@[expose] def orbSup (T : Subgroup (MulAut W)) (V : Subgroup W) : Subgroup W :=
  ⨆ t ∈ T, V.map t.toMonoidHom

@[expose] def conjAutSub (t : MulAut W) (X : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  X.map (MulAut.conj t).toMonoidHom

@[expose] def IsSumMod (C A B Tot : Subgroup W) : Prop :=
  Tot = A ⊔ B ⊔ C ∧ (A ⊔ C) ⊓ (B ⊔ C) ≤ C

end Vocab

section TensorModel

@[expose] def tensorAct (d : ℕ) (K : Type) [Field K]
    (g : ↥(StatedSL d K) × ↥(StatedSL d K)) (X : Multiplicative (Matrix (Fin d) (Fin d) K)) :
    Multiplicative (Matrix (Fin d) (Fin d) K) :=
  Multiplicative.ofAdd
    (((g.1 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) * Multiplicative.toAdd X *
      ((g.2 : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ)

@[expose] def FFModel.tensorNat (d : ℕ) (K : Type) [Field K] : FFModel where
  Gam := ↥(StatedSL d K) × ↥(StatedSL d K)
  Amb := Multiplicative (Matrix (Fin d) (Fin d) K)
  act := tensorAct d K
  sec := ⊤
  ker := ⊥

@[expose] def Omega4PlusModule {V : Type*} [CommGroup V] (H : Subgroup (MulAut V)) (n : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
    (FFModel.tensorNat 2 K).Realizes H ⊤ ⊥

@[expose] def TensorNatL32 {V : Type*} [CommGroup V] (H : Subgroup (MulAut V)) : Prop :=
  (FFModel.tensorNat 3 (ZMod 2)).Realizes H ⊤ ⊥

end TensorModel

section Hypotheses

variable {W : Type} [CommGroup W]

structure D31 (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  exp : ∀ w : W, w ^ 2 = 1
  qsqtk : IsQuotientOfSQTKTC ↥M
  sylow : IsSylowTwoOf T M
  comp : L ∈ cComp M
  quasi : CFSG.IsQuasisimple ↥L
  Mp_eq : Mp = conjClosure L T
  Mp_normal : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))
  irr : V ∈ IrrPlus Mp (⊤ : Subgroup W)
  o2inv : ∀ g ∈ pCoreOf 2 (Mp ⊔ T), ∀ v ∈ V, g v ∈ V
  gen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤

structure D3Std [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  hyp : D31 M Mp T L V
  qhat : qhatOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)
  irrT : V ∈ IrrPlusOn Mp (orbSup T V) T

end Hypotheses

@[expose] def D36Concl {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) ∧
  (IsSumMod (orbSup T V ⊓ fixV Mp) (commSub (orbSup T V) L)
      ((commSub (orbSup T V) L).map t.toMonoidHom) (orbSup T V) ∧
    ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ conjAutSub t L, g u = u) ∧
  qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ) ∧
  (commSub (orbSup T V) L = V ∨
    (IsPSL 3 2 1 ↥(autSub L (orbSup T V)) ∧
      (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
      (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
        IsIntDirect V (V.map s.toMonoidHom) (commSub (orbSup T V) L)) ∧
      Nat.card ↥V = 2 ^ 3))

@[expose] def D36cConcl {W : Type} [CommGroup W] [Finite W] (Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W) : Prop :=
  (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) ∧
  (IsSumMod (orbSup T V ⊓ fixV Mp) (commSub (orbSup T V) L)
      ((commSub (orbSup T V) L).map t.toMonoidHom) (orbSup T V) ∧
    ∀ u ∈ commSub (orbSup T V) L, ∀ g ∈ conjAutSub t L, g u = u) ∧
  qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ) ∧
  (commSub (orbSup T V) L = V ∨
    (IsPSL 3 2 1 ↥(autSub L (orbSup T V)) ∧
      (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) ∧
      (∀ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) → s ∉ stabSub V →
        commSub (orbSup T V) L = V ⊔ V.map s.toMonoidHom ∧
          IsSumMod (commSub (orbSup T V) L ⊓ fixV Mp) V (V.map s.toMonoidHom)
            (commSub (orbSup T V) L)) ∧
      Nat.card ↥V = 2 ^ 3 * Nat.card ↥(V ⊓ fixV Mp)))

@[expose] def D36c : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V < orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L →
      D36cConcl Mp T L V t ∨ D36cConcl Mp T (conjAutSub t L) V t⁻¹

@[expose] def D36B48q : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D3Std M Mp T L V → V < orbSup T V → t ∈ T →
    t ∉ Subgroup.normalizer (L : Set (MulAut W)) → Mp = L ⊔ conjAutSub t L →
    (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) →
    qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ) →
    IsPSL 3 2 1 ↥(autSub L (orbSup T V)) →
    (∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set (MulAut W)) ∧ s ∉ stabSub V) →
    V ⊓ fixV Mp = ⊥

@[expose] def D36 : Prop := D36c ∧ D36B48q

@[expose] def D37 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V = orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L →
      (∃ n, IsPSL 2 2 n ↥(autSub L V) ∧ Omega4PlusModule (autSub Mp V) n) ∨
      (IsPSL 3 2 1 ↥(autSub L V) ∧ TensorNatL32 (autSub Mp V))

@[expose] def D391 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    Mp = L → D3Std M Mp T L V → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
    (V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L)) →
    ∀ A : Subgroup (MulAut W), IsA2 M A → A ≤ T → commSeries A 3 = ⊥ → rAV A ≤ 2 →
      (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
      orbSup T V = ⊤ ∨ (V = orbSup T V ∧ IsFFModule (autSec (L ⊔ T) V (fixV Mp)))

@[expose] def D310Two {W : Type} [CommGroup W] (T L : Subgroup (MulAut W)) (V : Subgroup W) :
    Prop :=
  ((∃ n, BinaryNaturalSL L V (V ⊓ fixV L) 3 n) ∨ (∃ n, BinaryNaturalSp4 L V (V ⊓ fixV L) n) ∨
      AlternatingNatural L V (V ⊓ fixV L) 6 ∨ BinaryNaturalSL L V (V ⊓ fixV L) 4 1 ∨
      BinaryNaturalSL L V (V ⊓ fixV L) 5 1 ∨ A7Four L V (V ⊓ fixV L)) ∧
    (∃ t ∈ T, t ∉ stabSub V) ∧
    ∀ t ∈ T, t ∉ stabSub V →
      IsSumMod (fixV L) V (V.map t.toMonoidHom) ⊤ ∧
        ¬ SecIsoL L V (V ⊓ fixV L) (V.map t.toMonoidHom) (V.map t.toMonoidHom ⊓ fixV L)

@[expose] def D310 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
      (∀ t ∈ T, t ∈ stabSub V) ∨ D310Two T L V

@[expose] def D321Two {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  IsPSL 3 2 1 ↥L ∧ DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4

@[expose] def D321Three {W : Type} [CommGroup W] (Mp L : Subgroup (MulAut W)) : Prop :=
  ∃ n, IsPSL 2 2 n ↥L ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      DirectSumOfCopies L (commV L) (commV L ⊓ fixV Mp) (FFModel.nat (StatedSL 2 K)) 2

@[expose] def D321 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
      ∀ A : Subgroup (MulAut W), A ≤ T → A ≠ ⊥ → IsElemAbelian2 A → commSeries A 2 = ⊥ →
        rAV A ≤ 2 → (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
        A ⊓ centSub (orbSup T V) = ⊥ →
      orbSup T V = ⊤ ∨
        (IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
          commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L))

end CFSG.Quasithin
