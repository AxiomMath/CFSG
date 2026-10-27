module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.KG82CoverCore
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H

@[expose] def s828CommSub {V : Type} [CommGroup V] (Y : Subgroup (MulAut V)) (W : Subgroup V) :
    Subgroup V :=
  Subgroup.closure {x | ∃ y ∈ Y, ∃ w ∈ W, x = y w * w⁻¹}

@[expose] def s828BPrime {V : Type} [CommGroup V] (H X : Subgroup (MulAut V)) : Subgroup V :=
  commV X ⊔ commV (perfectCore (H ⊓ stabSub (fixV X))) ⊔ fixV X

@[expose] def MB0_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    ((BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) →
        mQuot ⊤ (s828BPrime H X) = 1) ∧
    ((MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) →
        mQuot ⊤ (s828BPrime H X) = 1) ∧
    ((MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) →
        mQuot ⊤ (s828BPrime H X) = 1) ∧
    ((MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3) →
        mQuot ⊤ (s828BPrime H X) = 2)

@[expose] def MB1_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    ((BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) →
        s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
          s828BPrime H X) ∧
    ((MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) →
        (s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X).relIndex
          (s828BPrime H X) = 2) ∧
    ((MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) →
        s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
          s828BPrime H X) ∧
    ((MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3) →
        s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
          s828BPrime H X)

@[expose] def MB3_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    ((BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
      (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) ∨
      (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) ∨
      (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3)) →
    ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))),
      ∀ b ∈ s828BPrime H X, x b * b⁻¹ ∈ fixV X

@[expose] def Sylow822VB_828 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k →
        mQuot (fsuV T I) (ch82B (fsuV T I) h) = k

end CFSG.Quasithin.H13
