module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828MBRow1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.E3

@[expose] def MB3Row2_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) →
      ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))),
        ∀ b ∈ s828BPrime H X, x b * b⁻¹ ∈ fixV X

@[expose] def MB3Row3_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) →
      ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))),
        ∀ b ∈ s828BPrime H X, x b * b⁻¹ ∈ fixV X

@[expose] def MB3Row4_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3) →
      ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))),
        ∀ b ∈ s828BPrime H X, x b * b⁻¹ ∈ fixV X

@[expose] def MB0Row2_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) →
      mQuot ⊤ (s828BPrime H X) = 1

@[expose] def MB0Row3_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) →
      mQuot ⊤ (s828BPrime H X) = 1

@[expose] def MB0Row4_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3) →
      mQuot ⊤ (s828BPrime H X) = 2

theorem mB3_828_holds (h2 : MB3Row2_828) (h3 : MB3Row3_828)
    (h4 : MB3Row4_828) : MB3_828 := by
  intro V _ _ H X hXN hXe hrow x hx b hb
  rcases hrow with h | h | h | h
  · exact mb3_row1_mb V H X hXN hXe h x hx b hb
  · exact h2 V H X hXN hXe h x hx b hb
  · exact h3 V H X hXN hXe h x hx b hb
  · exact h4 V H X hXN hXe h x hx b hb

theorem mB0_828_holds (h2 : MB0Row2_828) (h3 : MB0Row3_828)
    (h4 : MB0Row4_828) : MB0_828 := by
  intro V _ _ H X hXN hXe
  exact ⟨fun h => mb0_row1_mb V H X hXN hXe h, h2 V H X hXN hXe, h3 V H X hXN hXe,
    h4 V H X hXN hXe⟩

end CFSG.Quasithin.H13
