module

public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofLift
public import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS1517Gen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → Group.IsPerfect X → ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) →
    ¬ Sec4.IsoLThreePi X 2 2 →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
      sSup (invariantPiSubgroups ⊤ D (piCompl 3)) = ⊤

variable {G : Type} [Group G] [Finite G]

namespace Proof1517

theorem mem_scriptY4_L (h135 : Item135Simple) (h142 : Concl142R) (h1510 : Item1510R)
    (hbr : Sec16.Step169TwoBridge) (h138 : Item138N) (hgen : KS1517Gen) {A : Subgroup G}
    {c : G} {L Y : Subgroup G} (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y) :
    L ∈ scriptY4 A (lB A) := by
  obtain ⟨p, e, hp, he, hiso, hprod, -⟩ := hctx.concl1515
  have hLc := h.mem_thetaComponentsAt
  have hsimp := Proof1514.isSimpleGroup_of_isoLThreePi hLc he hiso
  have hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc).1
  obtain ⟨hAbE, hAb9⟩ := isElemAbelian_card_aBar h hctx
  have hgL := le_sSup_of_gen h hctx (hgen _ p e he hiso hperf
    (not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he hiso hprod)
    (not_isoLThreePi_two_two_of_ctx1514 h (h1510 G A c L h) hbr hctx) _ hAbE hAb9)
  have hLΔ := le_delta_of_le_sSup h142 h hgL
  obtain ⟨-, h9, -⟩ := point_facts h hctx
  have h3 : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  refine ⟨⟨fun htop => ?_, h.le_normalizer⟩,
    Sec16.eq_oPrimeResidualOf_of_isSimpleGroup (Sec6.isPerfect_of_mem_thetaComponentsAt hLc)
      hsimp h3,
    le_antisymm hLΔ (delta_le L), h135 G A c L h.toSec13Data (Or.inl ⟨p, e, hp, he, hiso⟩)⟩
  refine centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian h.toSec13Data.ne_one ?_
  rw [eq_top_iff, ← htop]
  exact h.toSec13Data.le_centralizer

end Proof1517

open Proof1517

theorem step1517Y0_of (h135 : Item135Simple) (h142 : Concl142R) (h152 : Item152R)
    (h1510 : Item1510R) (hbr : Sec16.Step169TwoBridge) (h138 : Item138N)
    (hgen : KS1517Gen) : Step1517Y0 := by
  intro G _ _ A c L h Y hctx X hX hLX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL4 := mem_scriptY4_L h135 h142 h1510 hbr h138 hgen h hctx
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hM
  have hM2 : M ∈ scriptY2 A := Sec16.normalizer_pCoreOf_mem_scriptY2 h.isSimpleGroup h.nonabelian hX
  have hLM : L ≤ M := hLX.trans (Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX.2
  have hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  obtain ⟨J, -, hLJ, hJ0⟩ := h152 G A c L h L hL4 M hM2 hLM hF
  obtain ⟨Y₀, hJY₀, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hJ0
  exact ⟨Y₀, hY₀, hLJ.trans hJY₀⟩

end CFSG.RankThree.PartTwo.Sec15
