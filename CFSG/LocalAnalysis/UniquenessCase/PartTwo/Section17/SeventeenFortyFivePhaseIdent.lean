module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.Quasithin.Background.RonanE43M23
import CFSG.GroupTheory.Fitting.PPrimeCoreGeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

theorem phase45_identify_five (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    {L : Type} [Group L] [Finite L] (hLs : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hLK : CFSG.Open.IsKGroup L) (h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup L))
    {M : Subgroup L} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 M) :
    Nonempty (L ≃* alternatingGroup (Fin 10)) ∨
      (∃ s : TauCeti.SporadicName, Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
        (d.1 = .tits ∨ d.1 = .suzuki 2 ∨ (d.1.characteristic = 5 ∧ RankOneIndex45 d.1)) := by
  have hFtop : CFSG.generalizedFitting L = ⊤ :=
    CFSG.Quasithin.RonanE43.generalizedFitting_eq_top_of_simple hLs hLnab
  have hFs : IsSimpleGroup ↥(CFSG.generalizedFitting L) := by
    rw [hFtop]
    exact (MulEquiv.isSimpleGroup_congr Subgroup.topEquiv).mpr hLs
  have h5F : 5 ∣ Nat.card ↥(CFSG.generalizedFitting L) := by
    rw [hFtop, Nat.card_congr (Subgroup.topEquiv (G := L)).toEquiv]
    exact hM.2.1.trans (Subgroup.card_subgroup_dvd_card M)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hO : CFSG.pPrimeCore 5 L = ⊥ :=
    CFSG.pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting hFs h5F
  have h := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.identification_of_isStronglyPEmbedded
    hId hLie hCyc (p := 5) (by norm_num) le_rfl hLK hO h2 hM
  rw [hFtop] at h
  have key : ∀ {Y : Type} [Group Y], Nonempty (↥(⊤ : Subgroup L) ≃* Y) → Nonempty (L ≃* Y) :=
    fun {Y} _ ⟨e⟩ => ⟨Subgroup.topEquiv.symm.trans e⟩
  rcases h with hS | ⟨d, hd, ⟨e⟩⟩ | ⟨-, hSz⟩
  ·
    unfold CFSG.AGLEmbedding.IsSmallStrongP at hS
    rcases hS with hLin | hUni | hAlt | h3 | hFive | h11
    ·
      unfold CFSG.AGLEmbedding.IsSmallLinTwo CFSG.AGLEmbedding.IsLinTwoIndex at hLin
      obtain ⟨d, ⟨q, hdq, hqp, -⟩, ⟨e⟩⟩ := hLin
      refine Or.inr (Or.inr ⟨d, ⟨key ⟨e⟩, Or.inr (Or.inr ⟨?_, q, Or.inl hdq⟩)⟩⟩)
      rw [hdq, TauCeti.LieTypeIndex.characteristic_A]
      exact hqp
    ·
      unfold CFSG.AGLEmbedding.IsSmallUnitary at hUni
      obtain ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ := hUni
      refine Or.inr (Or.inr ⟨d, ⟨key ⟨e⟩, Or.inr (Or.inr ⟨?_, q, Or.inr hdq⟩)⟩⟩)
      rw [hdq, TauCeti.LieTypeIndex.characteristic_twistedA]
      exact hqp
    ·
      unfold CFSG.AGLEmbedding.IsAltTwoP at hAlt
      exact Or.inl (key hAlt)
    ·
      exact absurd h3.1 (by norm_num)
    ·
      obtain ⟨-, hT | hSp | hFi⟩ := hFive
      · unfold CFSG.AGLEmbedding.IsTitsGroup at hT
        obtain ⟨d, hdt, ⟨e⟩⟩ := hT
        exact Or.inr (Or.inr ⟨d, ⟨key ⟨e⟩, Or.inl hdt⟩⟩)
      · unfold CFSG.AGLEmbedding.IsSporadicGroup at hSp
        exact Or.inr (Or.inl ⟨.McL, key hSp⟩)
      · unfold CFSG.AGLEmbedding.IsFi22 at hFi
        exact Or.inr (Or.inl ⟨.Fi22, key hFi⟩)
    ·
      exact absurd h11.1 (by norm_num)
  ·
    rcases hd with hdn | hU | h3
    · obtain ⟨n, -, hdn⟩ := hdn
      unfold CFSG.AGLEmbedding.IsLinTwoIndex at hdn
      obtain ⟨q, hdq, hqp, -⟩ := hdn
      refine Or.inr (Or.inr ⟨d, ⟨key ⟨e⟩, Or.inr (Or.inr ⟨?_, q, Or.inl hdq⟩)⟩⟩)
      rw [hdq, TauCeti.LieTypeIndex.characteristic_A]
      exact hqp
    · obtain ⟨hU, -⟩ := hU
      unfold CFSG.AGLEmbedding.IsUnitaryIndex at hU
      obtain ⟨q, hqp, hdq⟩ := hU
      refine Or.inr (Or.inr ⟨d, ⟨key ⟨e⟩, Or.inr (Or.inr ⟨?_, q, Or.inr hdq⟩)⟩⟩)
      rw [hdq, TauCeti.LieTypeIndex.characteristic_twistedA]
      exact hqp
    · unfold CFSG.AGLEmbedding.IsReeGTwoIndex at h3
      exact absurd h3.1 (by norm_num)
  ·
    obtain ⟨hv, ⟨e⟩⟩ := hSz
    exact Or.inr (Or.inr ⟨⟨.suzuki 2, hv⟩, ⟨key ⟨e⟩, Or.inr (Or.inl rfl)⟩⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
