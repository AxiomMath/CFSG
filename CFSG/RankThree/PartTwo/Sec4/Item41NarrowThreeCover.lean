module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverResidual
public import CFSG.RankThree.PartTwo.Census.TripleCoverSuz
public import CFSG.RankThree.PartOne.N143.LieLeaves
public import CFSG.RankThree.PartOne.N143.LieThree
public import CFSG.RankThree.PartOne.N143.LieHigh
public import CFSG.RankThree.PartOne.N143.HighEven
public import CFSG.RankThree.PartOne.N143.O7
public import CFSG.RankThree.PartOne.N143.LieE6
public import CFSG.RankThree.PartOne.N143.AltLeaves
public import CFSG.RankThree.PartOne.N143.SectionListLie
public import CFSG.RankThree.PartOne.S11c.ETypeRankThree
public import CFSG.RankThree.PartOne.S11c.Co1Cover
public import CFSG.RankThree.PartOne.MultRes.Sec68Closed
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.RankThree.PartTwo.Census.Sporadic.J3
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryFourThree
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.RankThree.PartOne.N143.AltRank
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartOne.N143.SecRankHard
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.Co1SplitLocalSubgroup
public import Certificates.Certificate8153
public import Certificates.Certificate8156
public import Certificates.Certificate8157
public import Certificates.Certificate8171
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti
open CFSG.Assembly.RankThreeEven (localRank projSU)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def Item4_1ThreeCoverMcLON : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → IsQuasisimple X →
    IsPGroup 3 (Subgroup.center X) → Subgroup.center X ≠ ⊥ →
    (Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)) →
    localRank 3 (X ⧸ Subgroup.center X) ≤ 3

namespace Item41Narrow

theorem item4_1ThreeCover_of_mcLON
    (hGA : GriessMultipliersAllModels) (hMcLON : Item4_1ThreeCoverMcLON) : Item4_1ThreeCover := by
  intro X _ _ hX hq hZ3 hZ
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have hnonab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := hq.2.2
  have h3 : 3 ∣ Nat.card (Subgroup.center X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hZ (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 3 hk0
  have hsmall' := hMcLON X hX hq hZ3 hZ
  obtain ⟨i, ⟨e⟩⟩ : ∃ i : CFSGIndex, Nonempty (X ⧸ Subgroup.center X ≃* i.Group) := by
    have : IsSimpleGroup ((⊤ : Subgroup X) ⧸ (Subgroup.center X).subgroupOf ⊤) :=
      (Census.quotientCenterEquiv X).isSimpleGroup
    obtain ⟨i, ⟨f⟩⟩ := hX.kGroup ⊤ _ this
    exact ⟨i, ⟨(Census.quotientCenterEquiv X).symm.trans f⟩⟩
  have htc : Census.IsThreeCenterCover X i.Group := ⟨hq, h3, ⟨e⟩⟩
  have hexG : 4 ≤ CFSG.twoLocalOddRank X → False :=
    Census.SectionFourHyp.false_of_four_le_twoLocalOddRank hX
  have hev : ∀ {A : Type} [Group A], (X ⧸ Subgroup.center X ≃* A) →
      (∀ (W : Type) [Group W] [Finite W] (H : Subgroup W) (K : Subgroup H) [K.Normal],
        Nonempty (H ⧸ K ≃* A) → 4 ≤ CFSG.Assembly.evenRank W) → False := by
    intro A _ f hA
    have := hA X ⊤ _ ⟨(Census.quotientCenterEquiv X).trans f⟩
    have := hX.evenRank_le
    omega
  have hP : ∀ {P : CFSGIndex → Prop}, PartOne.N143.OddCentralCoverRank3For P → P i →
      localRank 3 (X ⧸ Subgroup.center X) ≤ 3 := fun h hi =>
    (OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans
      (h X hX.kGroup hq.1 hX.evenRank_le (X ⧸ Subgroup.center X) hnonab (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
        (by rw [QuotientGroup.ker_mk']; exact hZ3) (by rw [QuotientGroup.ker_mk']; exact h3)
        ⟨i, hi, ⟨e⟩⟩)
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn => exact hP PartOne.N143.oddCentralCoverRank3For_alternating trivial
  | sporadic s =>
    have h2224 := PartOne.sectionsForceEvenRankFour_fi23_fi24prime
      PartOne.sectionsForceEvenRankFour_Fi22 PartOne.hasSection_fi23_fi22
      PartOne.hasSection_fi24prime_fi23
    cases s with
    | M22 =>
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
      refine (PartOne.N143.localRank_le_factorization Nat.prime_three).trans ?_
      have hc : Nat.card (X ⧸ Subgroup.center X) = 443520 := by
        rw [Nat.card_congr (e.trans b.symm).toEquiv]
        exact CFSG.Sporadic.Mathieu.card_M22
      rw [hc]
      by_contra h
      have h4 : 3 ^ 4 ∣ 443520 :=
        (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).2 (by omega)
      norm_num at h4
    | J3 =>
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
      rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
        (e.trans (b.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv)) Nat.prime_three]
      refine (CFSG.RankThree.PartTwo.Census.localRank_three_le_two_of_centralizer
        fun t ht h9 => ?_).trans (by norm_num)
      rw [CFSG.RankThree.PartTwo.Census.card_centralizer_j3P ht] at h9
      exact absurd h9 (by norm_num)
    | McL =>
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
      exact hsmall' (Or.inl ⟨e.trans b.symm⟩)
    | ONan =>
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
      exact hsmall' (Or.inr ⟨e.trans b.symm⟩)
    | Suz => exact (hexG (Census.tripleCoverSuzRankFour X htc)).elim
    | Ly => exact (hexG (Census.tripleCoverSporadicResidual.ly X htc)).elim
    | Co3 => exact (hexG (Census.tripleCoverSporadicResidual.co3 X htc)).elim
    | Co2 => exact (hexG (Census.tripleCoverSporadicResidual.co2 X htc)).elim
    | HN => exact (hexG (Census.tripleCoverSporadicResidual.hn X htc)).elim
    | Th => exact (hexG (Census.tripleCoverSporadicResidual.th X htc)).elim
    | Co1 =>
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
      let π : (⊤ : Subgroup X) →* X ⧸ Subgroup.center X :=
        (QuotientGroup.mk' (Subgroup.center X)).comp (⊤ : Subgroup X).subtype
      have hπ : Function.Surjective π := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) y
        exact ⟨⟨x, trivial⟩, rfl⟩
      have hker : π.ker ≤ Subgroup.center (⊤ : Subgroup X) := fun x hx => by
        have hx' : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hx
        exact Subgroup.mem_center_iff.mpr fun y =>
          Subtype.ext (Subgroup.mem_center_iff.mp hx' y)
      exact (hexG (PartOne.co1ActualArbitraryCentralCoversForceTwoLocalRankFour X ⊤ _ π hπ
        ⟨e.trans b.symm⟩ hker)).elim
    | Fi22 =>
      obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Fi22 ≃*
          SporadicName.Fi22.Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
      exact (hev (e.trans b.symm) PartOne.sectionsForceEvenRankFour_Fi22).elim
    | Fi23 =>
      obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Fi23 ≃*
          SporadicName.Fi23.Group) := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
      exact (hev (e.trans b.symm) h2224.1).elim
    | Fi24Prime =>
      obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Fi24Prime ≃*
          SporadicName.Fi24Prime.Group) := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
      exact (hev (e.trans b.symm) h2224.2).elim
    | B =>
      obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .B ≃*
          SporadicName.B.Group) := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
      exact (hev (e.trans b.symm) PartOne.sectionsForceEvenRankFour_B).elim
    | M =>
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
      have := PartOne.simplePresentationM_sections_of_B_section PartOne.sectionsForceEvenRankFour_B
        PartOne.simplePresentationMHasBSection_holds X ⊤ _ (X ⧸ Subgroup.center X) hnonab
        ⟨Census.quotientCenterEquiv X⟩ ⟨e.trans b.symm⟩
      have := hX.evenRank_le
      omega
    | M11 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | M12 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | M23 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | M24 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | J1 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | J2 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | HS => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | He => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | Ru => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
    | J4 => exact (Census.not_isThreeCenterCover_sporadic (by simp) htc).elim
  | lie d =>
    have hd := Census.tripleCoverLie_of_griess hGA d X htc
    have hHigh := PartOne.N143.oddCentralCoverRank3For_lieHigh
      PartOne.N143.noOddCentralCoverFor_highEven.rank
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      have hr1 : 1 ≤ r :=
        ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
      have htc' : 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 := hd
      rcases (show r = 2 ∨ 5 ≤ r by have := htc'.1; omega) with h2r | h5
      · exact hP PartOne.N143.oddCentralCoverRank3For_lieThree ⟨h2r, htc'.2⟩
      · exact hP hHigh ⟨h5, htc'⟩
    | twistedA r q =>
      have hr2 : 2 ≤ r :=
        ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
      have htc' : (3 ∣ r + 1 ∧ 3 ∣ q.card + 1) ∨ (r = 3 ∧ q.card = 3) := hd
      rcases htc' with ⟨h1, h2⟩ | ⟨rfl, hq3⟩
      · rcases (show r = 2 ∨ 5 ≤ r by omega) with h2r | h5
        · exact hP PartOne.N143.oddCentralCoverRank3For_lieThree ⟨h2r, h2⟩
        · exact hP hHigh ⟨h5, h1, h2⟩
      · obtain ⟨hp3, hf1⟩ := Census.eq_three_of_card_eq_three hq3
        have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = 3 :=
          (LieTypeIndex.characteristic_twistedA 3 q).trans hp3
        have he1 : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 1 :=
          (LieTypeIndex.fieldExponent_twistedA 3 q).trans hf1
        have hK : Nat.card (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
            (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)) = 9 := by
          rw [GaloisField.card _ _ (by rw [he1]; norm_num), hc, he1]
          norm_num
        have hq3' : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ^
            ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 3 := by rw [hc, he1]; rfl
        have e' := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
        rw [hq3'] at e'
        rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e' Nat.prime_three]
        exact (CFSG.RankThree.PartTwo.Census.localRankThreeU43 _ hK).trans (by norm_num)
    | B r q =>
      have htc' : r = 3 ∧ q.card = 3 := hd
      exfalso
      exact PartOne.N143.noOddCentralCoverFor_o7 X hX.kGroup hq.1 hX.evenRank_le
        (X ⧸ Subgroup.center X) hnonab (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact hZ3)
        (by rw [QuotientGroup.ker_mk']; exact h3) ⟨CFSGIndex.lie ⟨.B r q, hv⟩, htc', ⟨e⟩⟩
    | G2 q =>
      obtain ⟨hp3, hf1⟩ := Census.eq_three_of_card_eq_three hd
      have hK : Nat.card (ZMod 3) = q.card := by
        rw [Nat.card_zmod, PrimePower.card_def, hp3, hf1, pow_one]
      obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by rw [hp3]; decide) (ZMod 3) hK
      rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv (e.trans b.symm)
        Nat.prime_three]
      exact CFSG.RankThree.PartTwo.Census.Carrier.G2Three.localRank_three_adjointQuotient.trans
        (by norm_num)
    | E6 q =>
      exact hP (PartOne.N143.oddCentralCoverRank3For_lieE6
        PartOne.actualCoverETypeRankThreeOnlyE6FieldTwo CFSG.TauCetiBridge.Even.chevalleyBridgesAll)
        hd
    | twistedE6 q =>
      exact hP (PartOne.N143.oddCentralCoverRank3For_lieE6
        PartOne.actualCoverETypeRankThreeOnlyE6FieldTwo CFSG.TauCetiBridge.Even.chevalleyBridgesAll)
        hd
    | C r q => exact hd.elim
    | D r q => exact hd.elim
    | twistedD r q => exact hd.elim
    | E7 q => exact hd.elim
    | E8 q => exact hd.elim
    | F4 q => exact hd.elim
    | trialityD4 q => exact hd.elim
    | suzuki m => exact hd.elim
    | reeG2 m => exact hd.elim
    | reeF4 m => exact hd.elim
    | tits => exact hd.elim

end Item41Narrow

end CFSG.RankThree.PartTwo.Sec4
