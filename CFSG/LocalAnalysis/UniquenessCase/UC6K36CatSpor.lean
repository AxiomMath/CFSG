module

public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.S11c.Co1Cover
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.Sporadic.Bridge.Co1Surj
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Bridge.Fi24Surj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne

section Sections

theorem mem_sporadicsThm3_of_component {G : Type} [Group G] [Finite G]
    (he : ∀ q : ℕ, q.Prime → q ≠ 2 → twoLocalPrimeRank q G ≤ 3) {L : Subgroup G}
    (hL : CFSG.IsComponent L) {s : TauCeti.SporadicName}
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) : s ∈ sporadicsThm3 := by
  by_contra hs
  have hev : CFSG.Assembly.evenRank G ≤ 3 := CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le he
  have hq : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a := hL.1.2.2
  have h22 := sectionsForceEvenRankFour_Fi22
  have h2224 := sectionsForceEvenRankFour_fi23_fi24prime h22 hasSection_fi23_fi22 hasSection_fi24prime_fi23
  cases s
  case Co1 =>
    obtain ⟨b⟩ : Nonempty (Carrier .Co1 ≃* TauCeti.SporadicName.Co1.Group) :=
      CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
    have h4 := co1ActualArbitraryCentralCoversForceTwoLocalRankFour G L _
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _) ⟨φ.trans b.symm⟩
      (QuotientGroup.ker_mk' _).le
    rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
    omega
  case Fi22 =>
    obtain ⟨b⟩ : Nonempty (Carrier .Fi22 ≃* TauCeti.SporadicName.Fi22.Group) :=
      CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
    have h4 := h22 G L (Subgroup.center ↥L) ⟨φ.trans b.symm⟩
    omega
  case Fi23 =>
    obtain ⟨b⟩ : Nonempty (Carrier .Fi23 ≃* TauCeti.SporadicName.Fi23.Group) :=
      CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
    have h4 := h2224.1 G L (Subgroup.center ↥L) ⟨φ.trans b.symm⟩
    omega
  case Fi24Prime =>
    obtain ⟨b⟩ : Nonempty (Carrier .Fi24Prime ≃* TauCeti.SporadicName.Fi24Prime.Group) :=
      CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
    have h4 := h2224.2 G L (Subgroup.center ↥L) ⟨φ.trans b.symm⟩
    omega
  case B =>
    obtain ⟨b⟩ : Nonempty (Carrier .B ≃* TauCeti.SporadicName.B.Group) :=
      CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
    have h4 := sectionsForceEvenRankFour_B G L (Subgroup.center ↥L) ⟨φ.trans b.symm⟩
    omega
  case M =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
    have h4 := simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
      simplePresentationMHasBSection_holds G L (Subgroup.center ↥L) (↥L ⧸ Subgroup.center ↥L) hnab
      ⟨MulEquiv.refl _⟩ ⟨φ.trans b.symm⟩
    omega
  all_goals exact (hs (by simp [sporadicsThm3])).elim

end Sections

end CFSG.LocalAnalysis.UniquenessCase.UCK
