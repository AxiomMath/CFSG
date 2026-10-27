module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofZDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof15Res11

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem mem_scriptY4_of_j2
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    L ∈ scriptY4 A (lB A) := by
  have hD := h.toSec13Data
  have hS := h.toSec14Std
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hD.le_centralizer))
  have hperf := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  obtain ⟨eθ⟩ := hJ
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hsimp : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := eθ.isSimpleGroup
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_thetaQuot_j2 ⟨eθ⟩
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop) hperf ⟨eθ⟩
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_mulEquiv_nativeJ2 CFSG.Sporadic.J2.isSimpleGroup_J2
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) eJ
  exact ⟨⟨hLtop, hD.le_normalizer⟩, Sec16.eq_oPrimeResidualOf_of_isSimpleGroup hperf hsimp h3L,
    le_antisymm (Proof155w.le_delta_of_le_of_j2 hS ⟨eθ⟩ le_rfl) (delta_le L), hq⟩

theorem false_of_le_normalizer
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A ≠ {Subgroup.zpowers c}) (h152 : Item152 A (lB A))
    (h1514 : Item1514 A (lB A) c L) {U : Subgroup G} (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (U : Set G) with hMdef
  have hloc : IsPLocal 2 M := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hU2 hU1
  have hMtop : M ≠ ⊤ := Sec14.normalizer_ne_top_of_isPGroup h.toTheoremFourHyp.isSimpleGroup
    h.toTheoremFourHyp.nonabelian hU1 hU2
  have hUO : U ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU2
  have hM2 : M ∈ scriptY2 A :=
    ⟨⟨hMtop, hAU.trans Subgroup.le_normalizer⟩, fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUO))⟩
  have hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  have hL4 := mem_scriptY4_of_j2 h hJ
  obtain ⟨X, -, hLX, hX0⟩ := h152 L hL4 M hM2 hLU hF
  obtain ⟨Y₀, hXY, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hX0
  have hm : MeetsY4 A (lB A) L Y₀ := ⟨L, hL4, le_inf le_rfl (hLX.trans hXY)⟩
  obtain ⟨φ⟩ := hJ
  rcases h1514 Y₀ hY₀ hm with ⟨-, -, h3, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨_, ⟨e⟩⟩, -⟩
  · exact hΩ h3
  · exact (KFacts.KS14.ks17J2NotList.2.1.false (φ.symm.trans e)).elim
  · exact (KFacts.KS14.not_isLThreeEpsAt_j2 5 1 (Or.inr ⟨by norm_num, ⟨φ.symm.trans e⟩⟩)).elim

end Proof15Res11

open Proof15Res11

theorem step1523ZLoc_of
    (h152 : Item152R) (h1514 : Item1514HJR) (hK : KS1523HJTwo) : Step1523ZLoc := by
  intro G _ _ A c L h hJ hΩ d hdA hd1 hdc S hSc hS2 hAS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hS14 := h.toSec14Std
  have h152' := h152 G A c L h
  have h1514' := h1514 G A c L h hJ
  have hfalse := @false_of_le_normalizer G _ _ A L c h hJ hΩ h152' h1514'
  have hO : CFSG.Open.pCoreOf 2 L = ⊥ := by
    by_contra hne
    exact hfalse (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hne
      (hD.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hO' : CFSG.pCore 2 ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxO : (x : G) ∈ CFSG.Open.pCoreOf 2 L := (mem_pCoreOf_iff1523 x).mpr hx
    rw [hO, Subgroup.mem_bot] at hxO
    exact (Subgroup.mem_bot).mpr (Subtype.ext hxO)
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hD.le_centralizer))
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
    (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  have hLJ : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO'.symm)).trans
      eJ⟩
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hSc.trans (centralizer_le_normalizer_of_j2 hS14 hJ)
  have hCL : S ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra hne
    refine hfalse ((hS2.to_le inf_le_left)) hne ?_ ?_
    · exact Late.le_normalizer_inf hAS (hD.le_normalizer.trans
        (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L))
    · exact (Subgroup.le_centralizer_iff.mp inf_le_right).trans
        (Subgroup.centralizer_le_normalizer _)
  obtain ⟨-, hAL9, -⟩ := j2_point_facts hD hJ
  have hdL : d ∈ L := hdc.1
  exact hK G L (A ⊓ L) S d hLJ inf_le_right hAL9 ⟨hdA, hdL⟩ hd1 hdc hS2 hSL hCL
    (inf_le_left.trans hAS)

end CFSG.RankThree.PartTwo.Sec15
