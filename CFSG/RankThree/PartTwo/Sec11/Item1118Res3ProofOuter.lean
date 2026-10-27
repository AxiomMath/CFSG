module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofTriality
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStmt
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def NoOuterType424D4Odd : Prop :=
  NoOuterType424For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 2 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def NoOuterType424D4Three : Prop :=
  NoOuterType424For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def D4OuterStdNoType424 :
    Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fieldActor (t := TwistTag.D4) σ σ s = s → s ^ 3 = 1 →
        ¬ KS11Lie2Proof.HasType424
          (Sec4.autFix (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))

namespace Item1118Res3Proof

section Model


theorem exists_d4_model_pow {Z X : Type} [Group Z] [Group X] {q : TauCeti.PrimePower}
    {hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid}
    (f : X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)
    (e : Z ≃* _root_.commutator X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (q.p ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      Nonempty (Z ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p (3 * q.exponent)
  have hKp : CharP K q.p := inferInstanceAs (CharP (GaloisField q.p (3 * q.exponent)) q.p)
  have hK3 : Nat.card K = q.card ^ 3 := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
  set σ' : K ≃+* K := iterateFrobeniusEquiv K q.p q.exponent with hσ'def
  have hσ'y : ∀ y : K, σ' y = y ^ q.card := fun y => by
    rw [hσ'def, iterateFrobeniusEquiv_def, TauCeti.PrimePower.card_def]
  have hK3' : Nat.card K = q.card ^ TwistTag.D4.order := hK3
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hq K hK3'
    σ'.toRingHom hσ'y
  set L := AlgebraicClosure K
  have : CharP L q.p := @charP_of_injective_ringHom K L _ _ (algebraMap K L)
    (algebraMap K L).injective q.p hKp
  obtain ⟨-, -, hTG, hsimple, hnonab⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group q.p q.exponent q.prime_p
      q.exponent_pos K (by rw [hK3, TauCeti.PrimePower.card_def]) L 1 (Or.inl rfl) σ'.toRingHom
      (fun c => by rw [pow_one, ← TauCeti.PrimePower.card_def]; exact hσ'y c)
      (iterateFrobenius L q.p q.exponent) (fun c => iterateFrobenius_def q.p q.exponent c)
  set e3 := MulEquiv.subgroupCongr hTG
  have : IsSimpleGroup (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ'.toRingHom) :=
    MulEquiv.isSimpleGroup e3
  obtain ⟨e2⟩ := KS11Lie3Proof.nonempty_derivedCentralQuotient_mulEquiv
    (CFSG.Blueprint.twistedFixedGroup TwistTag.D4 K σ'.toRingHom) (by
      obtain ⟨x, y, hxy⟩ := hnonab
      refine ⟨e3.symm x, e3.symm y, fun h => hxy ?_⟩
      have := congrArg e3 h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)
  have hXp : Group.IsPerfect X := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 q hq
    exact Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  have hq' : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  refine ⟨K, inferInstance, inferInstance, σ', by rw [hK3, hq'], fun c => by
    rw [hσ'y, hq'], ⟨(e.trans ((MulEquiv.subgroupCongr hXp.commutator_eq_top).trans
      Subgroup.topEquiv)).trans (f.trans (b.symm.trans (e2.trans e3)))⟩⟩

theorem exists_d4_model_two {Z : Type} [Group Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X)) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σ c = c ^ 2 ^ n) ∧
      Nonempty (Z ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨X, _, ⟨q, hq, hp2, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  obtain ⟨K, _, _, σ, hK, hσ, hE⟩ := exists_d4_model_pow f e
  rw [hp2] at hK hσ
  exact ⟨q.exponent, K, inferInstance, inferInstance, σ, hK, hσ, hE⟩

end Model

end Item1118Res3Proof

section Even


theorem noOuterType424D4Even_holds :
    NoOuterType424For fun X _ => ∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group) := by
  intro Z _ _ hZ α J hα3 hαout hJ hJT
  obtain ⟨n, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item1118Res3Proof.exists_d4_model_two hZ
  have hK2 := Sec8.Item8KFactsProof.ringChar_eq_two_of_card hK
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set β := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβin : ¬ KFacts.IsInnerAut β := fun h => hαout ((KFacts.isInnerAut_congr e α).mp h)
  have hHas : KS11Lie2Proof.HasType424 (Item426.fixSub α) := KS11Lie2Proof.hasType424_of_mem hJ hJT
  have hfixα : Item426.fixSub α = Sec4.autFix α := by
    ext x
    rfl
  have hHasβ : KS11Lie2Proof.HasType424 (Sec4.autFix β) := by
    rw [hfixα] at hHas
    exact hHas.of_mulEquiv (Sec4.autFixCongrEquiv e α).symm
  rcases Sec8.kF82D4OuterClasses_of_lang Sec8.kF82D4LangCoset_holds n K σ hK hσ β hβ3 hβin with
    hstd | ⟨γ, y, hγ, hγy, hy, hβγ⟩
  · exact Sec4.Item424Res2.not_hasType424_autFix_of_isStdGraphFieldConj hK2 σ hstd hHasβ
  · rw [hβγ] at hHasβ
    exact Sec4.k424TrialitySecond_holds n K σ hK hσ γ y hγ hγy hy hHasβ

theorem noOuterType424D4_of_odd (hOdd : NoOuterType424D4Odd) : NoOuterType424D4 := by
  have h := KS11Lie2Proof.noOuterType424For_or noOuterType424D4Even_holds hOdd
  intro Z _ _ hZ α J hα3 hin hJ hJT
  obtain ⟨X, _, ⟨q, hq, hf⟩, he⟩ := hZ
  by_cases hp : q.p = 2
  · exact h Z ⟨X, inferInstance, Or.inl ⟨q, hq, hp, hf⟩, he⟩ α J hα3 hin hJ hJT
  · exact h Z ⟨X, inferInstance, Or.inr ⟨q, hq, hp, hf⟩, he⟩ α J hα3 hin hJ hJT

theorem noOuterType424D4Odd_of (hNF : GH74.GLS.Stage2.Bender.Thm1.D4CocycleNF)
    (hStd : D4OuterStdNoType424) (h3 : NoOuterType424D4Three) : NoOuterType424D4Odd := by
  intro Z _ _ hZ α J hα3 hαout hJ hJT
  obtain ⟨X, _, ⟨q, hqv, hp2, ⟨f⟩⟩, ⟨e⟩⟩ := hZ
  by_cases hp3 : q.p = 3
  · exact h3 Z ⟨X, inferInstance, ⟨q, hqv, hp3, ⟨f⟩⟩, ⟨e⟩⟩ α J hα3 hαout hJ hJT
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Item1118Res3Proof.exists_d4_model_pow f e
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set β := MulAut.congr E α with hβ
    have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
    have hβout : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
      fun h => hαout ((KFacts.isInnerAut_congr E α).mp h)
    have hβ1 : β ≠ 1 := fun h => hβout ⟨1, by rw [h, map_one]⟩
    have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
    have hHas : KS11Lie2Proof.HasType424 (Item426.fixSub α) :=
      KS11Lie2Proof.hasType424_of_mem hJ hJT
    have hfixα : Item426.fixSub α = Sec4.autFix α := by
      ext x
      rfl
    have hHasβ : KS11Lie2Proof.HasType424 (Sec4.autFix β) := by
      rw [hfixα] at hHas
      exact hHas.of_mulEquiv (Sec4.autFixCongrEquiv E α).symm
    have hfixinv : ∀ ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        Sec4.autFix ρ⁻¹ = Sec4.autFix ρ := by
      intro ρ
      ext x
      rw [Sec4.mem_autFix, Sec4.mem_autFix]
      constructor
      · intro h
        have := congrArg ρ h
        rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
        exact this.symm
      · intro h
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact h.symm
    have hcongr : ∀ (γ ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        γ * ρ * γ⁻¹ = MulAut.congr γ ρ := by
      intro γ ρ
      ext x
      rfl
    obtain ⟨g, hg, hβg⟩ := GH74.GLS.Stage2.Bender.Thm1.d4_outer_three_normal_form q.prime_p hp2
      q.exponent_pos K hK σ hσ β hβord hβout
    obtain ⟨y, s', hs'σ, hs'3, hys⟩ :=
      hNF q.p q.exponent q.prime_p hp2 hp3 q.exponent_pos K hK σ hσ g hg
    have hHasg : KS11Lie2Proof.HasType424
        (Sec4.autFix (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)) := by
      rcases hβg with h | h
      · rw [← h]
        exact hHasβ
      · rw [← h, hfixinv]
        exact hHasβ
    apply hStd q.p q.exponent q.prime_p hp2 hp3 q.exponent_pos K hK σ hσ s' hs'σ hs'3
    rw [← hys, hcongr]
    exact hHasg.of_mulEquiv (Sec4.autFixCongrEquiv (MulAut.conj y) _).symm

theorem noOuterType424D4_of_parts (hNF : GH74.GLS.Stage2.Bender.Thm1.D4CocycleNF)
    (hStd : D4OuterStdNoType424) (h3 : NoOuterType424D4Three) : NoOuterType424D4 :=
  noOuterType424D4_of_odd (noOuterType424D4Odd_of hNF hStd h3)

end Even

end CFSG.RankThree.PartTwo.Sec11
