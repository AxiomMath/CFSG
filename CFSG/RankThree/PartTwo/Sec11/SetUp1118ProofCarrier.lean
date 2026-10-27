module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.Blueprint.Chevalley
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec11.SetUp1118Proof


theorem isPerfect_lie_G2 (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid) :
    Group.IsPerfect (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq
    (GaloisField q.p q.exponent) hK
  have h3 : 3 ≤ Nat.card (GaloisField q.p q.exponent) := by
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at h1
    rw [hK]
    exact h1
  have := (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card
    (GaloisField q.p q.exponent) h3).1
  have : Group.IsPerfect (CFSG.Blueprint.AdjointQuotient .G2 (GaloisField q.p q.exponent)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective

theorem isPerfect_lie_trialityD4 (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    Group.IsPerfect (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p (3 * q.exponent)
  have hK3 : Nat.card K = q.card ^ 3 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  have hK : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := hK3
  let σ : K →+* K := iterateFrobenius K q.p q.exponent
  have hσ : ∀ y, σ y = y ^ q.card := fun y => by
    rw [TauCeti.PrimePower.card_def]
    exact iterateFrobenius_def q.p q.exponent y
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).trialityD4 q hq K hK σ hσ
  have hq2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  have := (CFSG.LieType.Steinberg.TwistedD4.isQuasisimple_derived_twistedFixedGroup_D4 σ hq2 hK3
    hσ).1
  have : Group.IsPerfect (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup .D4 K σ)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective

end CFSG.RankThree.PartTwo.Sec11.SetUp1118Proof
