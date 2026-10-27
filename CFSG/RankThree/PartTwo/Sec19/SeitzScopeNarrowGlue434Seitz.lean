module

public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSeitz199
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitz434
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

@[expose] def Seitz199L3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup (MulAut X)),
    (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 →
    (CFSG.IsQuasisimple X ∧ Sec4.IsSLThreePi X ∧
        ¬ (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
          D ≤ (MulAut.conj : X →* MulAut X).range)) →
    Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x = x} = ⊤

@[expose] def Seitz199D4Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Subgroup (MulAut X)),
    (∀ φ ∈ D, φ ^ 3 = 1) → Nat.card D = 9 →
    (∃ f : ℕ, CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) →
    Subgroup.closure {x : X | ∃ φ ∈ D, φ ≠ 1 ∧ φ x = x} = ⊤

theorem seitz199L3_of_seitzThree
    (hA : SeitzThreeLThreePi)
    (hO : Seitz199Outer) : Seitz199L3 := by
  intro X _ _ D hD3 hD9 ⟨hq, hSL, hnot⟩
  have hD := Item19ResProof.isElemAbelian_of_pow_three hD3 hD9
  by_cases hfix : FixCube D
  · obtain ⟨q, K, _, _, ⟨hKq, hq1, ⟨ι⟩⟩ | ⟨hKq, hq2, ⟨ι⟩⟩⟩ := hSL
    · exact Item19ResProof.closure_fixSet_sl_of_fixCube hKq hq1 ι D hD hD9 hfix
    · obtain ⟨p, f, hU, hq3, hq2', ⟨ι'⟩⟩ := Item19ResProof.exists_unitary_model hq hKq hq2 ι
      exact Item19ResProof.closure_fixSet_su_of_fixCube hU hq3 hq2' ι' D hD hD9 hfix
  have hnfix : ∃ e ∈ D, ∃ s : X, s ^ 3 = 1 ∧ MulAut.conj s ∈ D ∧ e s ≠ s := by
    unfold FixCube at hfix
    push Not at hfix
    obtain ⟨e, he, s, hs3, hsD, hes⟩ := hfix
    exact ⟨e, he, s, hs3, hsD, hes⟩
  by_cases hinn : D ≤ (MulAut.conj : X →* MulAut X).range
  · obtain ⟨q, K, _, _, ⟨hKq, hq1, ⟨ι⟩⟩ | ⟨hKq, hq2, ⟨ι⟩⟩⟩ := hSL
    · have hq4 : q ≠ 4 := by
        rintro rfl
        exact hnot ⟨Item19ResProof.nonempty_mulEquiv_sl34 hKq ι, hinn⟩
      have h := SeitzScopeProof.kGenTwoMod_and_card_center_sl_scope hA hq hKq hq1 hq4 ι
      exact Item19ResProof.closure_fixSet_of_inner h.2 h.1 hD hD9 hinn hnfix
    · obtain ⟨p, f, hU, hq3, hq2', ⟨ι'⟩⟩ := Item19ResProof.exists_unitary_model hq hKq hq2 ι
      have h := SeitzScopeProof.kGenTwoMod_and_card_center_su_scope hA hq hU hq3 hq2' ι'
      exact Item19ResProof.closure_fixSet_of_inner h.2 h.1 hD hD9 hinn hnfix
  · exact hO X D hD3 hD9 hq hSL hinn hnfix

section Certs

namespace SeitzScopeProof

open TauCeti CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

theorem closure_fixSet_of_trialityD4_char2
    (hS : SeitzPlanes fun d p _ => p = 3 ∧ IsTrialityIndex d.1 ∧ d.1.characteristic = 2)
    {X : Type} [Group X] {f : ℕ}
    (hmod : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f)
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    Subgroup.closure (fixSet D) = ⊤ := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨ι⟩⟩ := hmod
  set q : PrimePower := ⟨2, f, hp, by omega⟩ with hqdef
  have hv : (LieTypeIndex.trialityD4 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp
  have hK' : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [hK, PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
  obtain ⟨e⟩ : Nonempty (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup .D4 K σ) ≃*
        ValidLieTypeIndex.Group ⟨LieTypeIndex.trialityD4 q, hv⟩) :=
    CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv rfl K hK' σ hσ'
  have hc2 : (LieTypeIndex.trialityD4 q).characteristic = 2 := by
    rw [LieTypeIndex.characteristic_trialityD4]
  refine closure_fixSet_eq_top_of_seitzPlanes hS (d := ⟨.trialityD4 q, hv⟩) ?_ ?_ (ι.trans e) D
    hD hD9 ⟨rfl, ⟨q, rfl⟩, hc2⟩
  · change 3 ≠ (LieTypeIndex.trialityD4 q).characteristic
    rw [hc2]
    norm_num
  · simp [IsD2SeitzException]

end SeitzScopeProof

end Certs

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores

section CertsD4

namespace Item434RowsProof

theorem seitzHyperGamma_eq_top_of_D4_narrow (h199 : Sec19.Seitz199D4Two) {X : Type} [Group X]
    [Finite X] (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (hL : IsLie42GenericD4 (X ⧸ Subgroup.center X)) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : Nat.card E = 9) :
    CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨q, hv, hq2, -, -, ⟨θ⟩⟩ := hL
  have : Group.IsPerfect X := hq.1
  have hmod : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .trialityD4 2
      q.exponent :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv θ
      (Census.bridgeExceptional46.trialityD4 q hv hq2)
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  have hker : π.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  have hZ : Subgroup.center X = ⊥ := by
    rw [← hker]
    exact CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hmod π
      (QuotientGroup.mk'_surjective _) (by rw [hker]) (by rw [hker]; exact hodd)
  have eX : X ≃* X ⧸ Subgroup.center X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hmodX : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 q.exponent :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eX hmod
  exact seitzHyperGamma_eq_top_of_closure hE.2 h9 (h199 X E hE.2 h9 ⟨q.exponent, hmodX⟩)

end Item434RowsProof

end CertsD4

section CertsRest

theorem seitz434_of_rest_narrow (h199 : Sec19.Seitz199D4Two) (h : Seitz434Rest) : Seitz434 := by
  intro X _ _ hq hZ hL E hE hc
  have h9 : 9 ≤ Nat.card E := by rcases hc with h9 | ⟨h27, -⟩ <;> omega
  rcases isLie42Generic_cases hL with h2 | ⟨m, hm, -, hsz⟩ | hv | hr
  · exact seitzHyperGamma_eq_top_of_L2 X hq hZ h2 E hE hc
  · exact (Item434RowsProof.false_of_suzuki hq hZ hsz hE h9).elim
  · have := Item434RowsProof.card_le_three_of_L3Vac hq hZ hv hE.2
    omega
  · by_cases hD4 : IsLie42GenericD4 (X ⧸ Subgroup.center X)
    · rcases hc with h9 | ⟨h27, hZ1⟩
      · exact Item434RowsProof.seitzHyperGamma_eq_top_of_D4_narrow h199 hq hZ hD4 hE h9
      · exact h X hq hZ hr E hE (Or.inr ⟨h27, hZ1⟩)
    · exact h X hq hZ hr E hE (hc.imp (fun h9 => ⟨h9, hD4⟩) id)

end CertsRest

end CFSG.RankThree.PartTwo.Sec4
