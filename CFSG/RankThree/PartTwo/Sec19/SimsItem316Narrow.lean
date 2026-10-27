module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Sec19.F194Item316Glue
import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaPlanes
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.A4
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.CGT.PushingUp.BlockOrder
import CFSG.CGT.PushingUpLit.BHS7.BlockComm
import CFSG.CGT.PushingUpLit.BHS7.SevenThree
import CFSG.CGT.PushingUpLit.BHS7.VFacts
import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Monster.Code.Weights
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.RankThree.PartTwo.Sec19.Narrow316

open CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem pRank_three_le_evenRank {M : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M) :
    CFSG.Open.pRank 3 M ≤ CFSG.Open.evenRank G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨3, M, Nat.prime_three, by norm_num, hM.1, rfl⟩
  rintro _ ⟨p, H, hp, -, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp H).trans
    (Subgroup.card_le_card_group H)

theorem pRank_three_le_of_le (he : CFSG.Open.evenRank G = 3) {M L : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) (hLM : L ≤ M) : CFSG.Open.pRank 3 L ≤ 3 :=
  (CFSG.SectionRank.pRank_mono (by norm_num) hLM).trans (he ▸ pRank_three_le_evenRank hM)

theorem pRank_top_le_of_ker_eq_pCore {L : Subgroup G} {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (α : L →* A) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 L) :
    CFSG.Open.pRank p (⊤ : Subgroup A) ≤ CFSG.Open.pRank p L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    CFSG.SectionRank.pRank_quotient_eq _ hN, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

theorem statedScalars_zmod_two_eq_bot (ι : Type) [Fintype ι] [DecidableEq ι] :
    CFSG.Open.StatedScalars ι (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim u 1, map_one]

theorem pRank_statedProj_zmod_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) (p : ℕ) [Fact p.Prime] :
    CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.StatedProj H)) =
      CFSG.Open.pRank p (⊤ : Subgroup H) := by
  refine CFSG.SectionRank.pRank_quotient_eq _ ?_
  rw [statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf, Subgroup.card_bot]
  exact Nat.Prime.not_dvd_one Fact.out

theorem four_le_pRank_omegaPlusTwo {m : ℕ} (hm : 4 ≤ m) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (omegaPlusTwo m)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaPlus (K := ZMod 2) hm
  rwa [pRank_statedProj_zmod_two] at h

theorem four_le_pRank_omegaMinusTwo {m : ℕ} (hm : 4 ≤ m) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (omegaMinusTwo m)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Census194.RonanC194.OmegaEven.four_le_pRank_three_omegaMinus (K := ZMod 2)
    (n := m + 1) (by omega) 1 1
  rwa [pRank_statedProj_zmod_two] at h

theorem lt_four_of_isOmegaPlusType (he : CFSG.Open.evenRank G = 3) {M L : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) (hLM : L ≤ M) {m : ℕ} (h : IsOmegaPlusType L m) : m < 4 := by
  by_contra h4
  obtain ⟨α, hα, hker, -⟩ := h
  have h1 := four_le_pRank_omegaPlusTwo (m := m) (by omega)
  have h2 := pRank_top_le_of_ker_eq_pCore Nat.prime_three (by norm_num) α hα hker
  have h3 := pRank_three_le_of_le he hM hLM
  omega

theorem lt_four_of_isOmegaMinusType (he : CFSG.Open.evenRank G = 3) {M L : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) (hLM : L ≤ M) {m : ℕ} (h : IsOmegaMinusType L m) : m < 4 := by
  by_contra h4
  obtain ⟨α, hα, hker, -⟩ := h
  have h1 := four_le_pRank_omegaMinusTwo (m := m) (by omega)
  have h2 := pRank_top_le_of_ker_eq_pCore Nat.prime_three (by norm_num) α hα hker
  have h3 := pRank_three_le_of_le he hM hLM
  omega

theorem le_eleven_of_isAltNaturalType (he : CFSG.Open.evenRank G = 3) {M L : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) (hLM : L ≤ M) {n : ℕ} (h : IsAltNaturalType L n) :
    n ≤ 11 := by
  by_contra h12
  obtain ⟨α, hα, hker, -⟩ := h
  have h1 := Item19Res3Proof.four_le_pRank_alternatingGroup (N := n) (by omega)
  have h2 := pRank_top_le_of_ker_eq_pCore Nat.prime_three (by norm_num) α hα hker
  have h3 := pRank_three_le_of_le he hM hLM
  omega

theorem not_isPerfect_alternatingGroup_four : ¬ Group.IsPerfect (alternatingGroup (Fin 4)) := by
  intro hP
  let V : Subgroup (alternatingGroup (Fin 4)) :=
    { carrier := {x | x ^ 2 = 1}
      one_mem' := one_pow 2
      mul_mem' := fun {a b} ha hb =>
        CFSG.SignalizerFunctorTheorem.McBride.PSL2Three.a4_mul_sq a b ha hb
      inv_mem' := fun {a} ha => by
        change a⁻¹ ^ 2 = 1
        rw [inv_pow, show a ^ 2 = 1 from ha, inv_one] }
  have hle : commutator (alternatingGroup (Fin 4)) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def]
    exact CFSG.SignalizerFunctorTheorem.McBride.PSL2Three.a4_comm_sq x y
  have hall : ∀ x : alternatingGroup (Fin 4), x ^ 2 = 1 := fun x =>
    hle (Group.IsPerfect.mem_commutator (G := alternatingGroup (Fin 4)) (g := x))
  have h4 := CFSG.SignalizerFunctorTheorem.McBride.PSL2Three.a4_card_sq
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall),
    CFSG.SignalizerFunctorTheorem.McBride.PSL2Three.a4_card] at h4
  omega

theorem ne_four_of_isAltNaturalType {L : Subgroup G} {n : ℕ}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (h : IsAltNaturalType L n) : n ≠ 4 := by
  rintro rfl
  obtain ⟨α, hα, hker, -⟩ := h
  have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := hq.1
  let ᾱ : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin 4) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) α hker.ge
  have hᾱ : Function.Surjective ᾱ := by
    intro y
    obtain ⟨x, rfl⟩ := hα y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), QuotientGroup.lift_mk _ _ _⟩
  exact not_isPerfect_alternatingGroup_four (Group.IsPerfect.ofSurjective hᾱ)

theorem mem_of_isAltNaturalType_of_even (he : CFSG.Open.evenRank G = 3) {M L : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) (hLM : L ≤ M) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {n : ℕ} (h : IsAltNaturalType L n) (hev : Even n) : n = 6 ∨ n = 8 ∨ n = 10 := by
  have h3 := three_le_of_isAltNaturalType hq h
  have h11 := le_eleven_of_isAltNaturalType he hM hLM h
  have h4 := ne_four_of_isAltNaturalType hq h
  obtain ⟨k, rfl⟩ := hev
  omega

end CFSG.RankThree.PartTwo.Sec19.Narrow316
