module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofCenter
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.Adapters.TauCetiExceptional.EvenAll

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def CentJ119InnFor (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z b : Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      (∃ k : ℕ, b ^ 3 ^ k = 1) → b * z = z * b →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      (∀ j ∈ J, b * j = j * b) →
        b ^ (3 ^ (Nat.card J).factorization 3) = 1

@[expose] def CentJ119OutFor (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z : Z) (β : MulAut Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      (∃ k : ℕ, β ^ 3 ^ k = 1) → MulAut.conj z * β = β * MulAut.conj z →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      (∀ j ∈ J, β j = j) →
        β ∈ (MulAut.conj : Z →* MulAut Z).range

namespace KS11Lie3Proof

theorem mem_center_of_conj_eq_one {Z : Type} [Group Z] {x : Z} (h : MulAut.conj x = 1) :
    x ∈ Subgroup.center Z := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun φ : MulAut Z => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc g * x = x * g * x⁻¹ * x := by rw [h1]
    _ = x * g := by group

theorem centJ119For_of_inn_out {F : ∀ (X : Type) [Group X], Prop}
    (hZ1 : ∀ (Z : Type) [Group Z],
      (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
        Subgroup.center Z = ⊥)
    (hI : CentJ119InnFor F) (hO : CentJ119OutFor F) : CentJ119For F := by
  intro Z _ _ hZ z β J hz3 hβ hzβ hJ hJT hβJ
  obtain ⟨b, rfl⟩ := hO Z hZ z β J hz3 hβ hzβ hJ hJT hβJ
  have hc := hZ1 Z hZ
  obtain ⟨k, hk⟩ := hβ
  have hbk : b ^ 3 ^ k = 1 := by
    have h1 := mem_center_of_conj_eq_one (x := b ^ 3 ^ k) (by rw [map_pow, hk])
    rwa [hc, Subgroup.mem_bot] at h1
  have hbz : b * z = z * b := by
    have h1 : MulAut.conj (z * b * (b * z)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hzβ, mul_inv_cancel]
    have h2 := mem_center_of_conj_eq_one h1
    rw [hc, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2.symm
  have hbJ : ∀ j ∈ J, b * j = j * b := by
    intro j hj
    have h1 : b * j * b⁻¹ = j := hβJ j hj
    calc b * j = b * j * b⁻¹ * b := by group
      _ = j * b := by rw [h1]
  rw [← map_pow, hI Z hZ z b J hz3 ⟨k, hbk⟩ hbz hJ hJT hbJ, map_one]


theorem center_eq_bot_g2 (Z : Type) [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) : Subgroup.center Z = ⊥ := by
  obtain ⟨X, _, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  have hX := Item1119StepsProof.center_eq_bot_of_isoGTwo hXp (q := q) ⟨hq, ⟨f⟩⟩
  exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
    (e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)) hX

theorem center_eq_bot_d4 (Z : Type) [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) : Subgroup.center Z = ⊥ := by
  obtain ⟨X, _, ⟨q, hq, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (3 * q.exponent)) =
      q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [GaloisField.card q.p _ (by have := q.exponent_pos; omega), TauCeti.PrimePower.card_def]
    change q.p ^ (3 * q.exponent) = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hq
    (GaloisField q.p (3 * q.exponent)) hK
    (iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent)
    (fun x => by rw [TauCeti.PrimePower.card_def]; rfl)
  have e' := f.trans b.symm
  have hP := Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  have hX := KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e'
    (Item1119StepsProof.center_quotient_center_eq_bot_of_isPerfect hP)
  exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
    (e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv)) hX

end KS11Lie3Proof

@[expose] def CentJ119G2Inn : Prop :=
  CentJ119InnFor fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def CentJ119G2Out : Prop :=
  CentJ119OutFor fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def CentJ119D4Inn : Prop :=
  CentJ119InnFor fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def CentJ119D4Out : Prop :=
  CentJ119OutFor fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

end CFSG.RankThree.PartTwo.Sec11
