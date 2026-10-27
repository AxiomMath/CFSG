module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFacts
public import CFSG.RankThree.PartTwo.Sec12.Hering129HLift
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Cent
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Hering129KModels


theorem exists_adjoint_model {X : Type} [Group X] {r : TauCeti.PrimePower}
    (hX : Sec4.IsoGTwo X r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = r.card ∧ ringChar K = r.p ∧
      Nonempty (X ≃* adjointGroup .G2 K) := by
  obtain ⟨hq, ⟨f⟩⟩ := hX
  have : Fact r.p.Prime := ⟨r.prime_p⟩
  set K := GaloisField r.p r.exponent
  have hK : Nat.card K = r.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ r.exponent_pos.ne'
  have hKp : ringChar K = r.p :=
    ringChar.eq K r.p
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 r hq K hK
  exact ⟨K, inferInstance, inferInstance, hK, hKp,
    ⟨(f.trans b.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)⟩⟩

theorem exists_d4_model {X : Type} [Group X] {r : TauCeti.PrimePower}
    {hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid}
    (f : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = r.card ^ 3 ∧ (∀ c, σ c = c ^ r.card) ∧
      Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hXp : Group.IsPerfect X := by
    have := Sec11.SetUp1118Proof.isPerfect_lie_trialityD4 r hr
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  let e : X ≃* _root_.commutator X :=
    ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans Subgroup.topEquiv).symm
  obtain ⟨K, hK1, hK2, σ, hK, hσ, hE⟩ := Sec11.Item1118Res3Proof.exists_d4_model_pow f e
  refine ⟨K, hK1, hK2, σ, ?_, fun c => ?_, hE⟩
  · rw [hK, TauCeti.PrimePower.card_def]
  · rw [hσ c, TauCeti.PrimePower.card_def]

theorem isSimpleGroup_of_isG2D4 {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) : IsSimpleGroup X := by
  rcases h with ⟨-, hX⟩ | ⟨-, hr, ⟨f⟩⟩
  · obtain ⟨K, hK1, hK2, hK, -, ⟨e⟩⟩ := exists_adjoint_model hX
    obtain ⟨hv, -⟩ := hX
    haveI := CFSG.LieType.SeitzGeneration.isSimpleGroup_adjointGroup_G2 r hv K hK
    exact e.isSimpleGroup
  · obtain ⟨K, hK1, hK2, σ, hK, hσ, ⟨e⟩⟩ := exists_d4_model f
    haveI : Fact r.p.Prime := ⟨r.prime_p⟩
    have hcard : Nat.card K = (r.p ^ r.exponent) ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
    have hσ' : ∀ c, σ c = c ^ (r.p ^ r.exponent) := fun c => by
      rw [hσ c, TauCeti.PrimePower.card_def]
    haveI := Sec11.Item1120V0Bar.isSimpleGroup_graphFixedRootGroup_d4 (K := K) (σ := σ)
      (ℓ := r.p) (f := r.exponent) r.exponent_pos hcard hσ'
    exact e.isSimpleGroup

theorem isPerfect_of_isG2D4 {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) : Group.IsPerfect X := by
  rcases h with ⟨-, hX⟩ | ⟨-, hr, ⟨f⟩⟩
  · obtain ⟨K, hK1, hK2, hK, -, ⟨e⟩⟩ := exists_adjoint_model hX
    obtain ⟨hv, -⟩ := hX
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K h3
    haveI : Group.IsPerfect (adjointGroup .G2 K) := hq.1
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have := Sec11.SetUp1118Proof.isPerfect_lie_trialityD4 r hr
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective

theorem exists_noncomm_of_perfect {S : Type} [Group S] [Nontrivial S] (hp : Group.IsPerfect S) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  letI : CommGroup S := { ‹Group S› with mul_comm := hcon }
  haveI : Group.IsPerfect S := hp
  exact Group.IsPerfect.not_isSolvable S inferInstance

theorem center_eq_bot_of_isG2D4 {X : Type} [Group X] {r : TauCeti.PrimePower} {δ : ℕ}
    (h : IsG2D4 X r δ) : Subgroup.center X = ⊥ := by
  haveI := isSimpleGroup_of_isG2D4 h
  exact Hering129HLift.center_eq_bot_of_simple (isSimpleGroup_of_isG2D4 h)
    (exists_noncomm_of_perfect (isPerfect_of_isG2D4 h))

end Hering129KModels

end CFSG.RankThree.PartTwo.Sec12
