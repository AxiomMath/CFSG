module

public import CFSG.RankThree.PartTwo.Sec18.Item187R
import CFSG.RankThree.PartTwo.Sec18.Item187Syl
import CFSG.RankThree.PartTwo.Sec18.Item187Gen
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.RankThree.PartTwo.Sec18.Item187Min

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.le_M (hX : MinCex A M H c X) : X ≤ M :=
  le_of_le_normalizer_of_isPiSubgroup hX.sec18H.toSec18Std hX.isPiSubgroup
    (le_sup_left.trans hX.le_normalizer)

theorem MinCex.not_three_dvd (hX : MinCex A M H c X) : ¬ 3 ∣ Nat.card X := fun h3 => by
  have hmem : (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ piCompl 3 :=
    hX.isPiSubgroup ⟨3, Nat.prime_three⟩ h3
  exact hmem rfl

theorem MinCex.orderOf_c (h184 : Item184_1) (hX : MinCex A M H c X) : orderOf c = 3 :=
  orderOf_eq_three_of_sec18H h184 hX.sec18H

theorem MinCex.pCoreOf_le_S (h186 : Item186H) (hX : MinCex A M H c X) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
  (pCoreOf_le_pCoreOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem (MinCex.le_M hX)).2

theorem MinCex.centralizer_pCoreOf_le (h186 : Item186H) (hX : MinCex A M H c X) :
    X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ CFSG.Open.pCoreOf 2 X :=
  inf_centralizer_le_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem (MinCex.le_M hX)

theorem MinCex.pRank_five_le (hX : MinCex A M H c X) : CFSG.pRank 5 ↥X ≤ 2 := by
  have hM2 : CFSG.Open.IsTwoLocal M := (mem_scriptM_iff.mp hX.sec18H.mem_scriptM).1.1
  have h1 : CFSG.pRank 5 ↥X = CFSG.Open.pRank 5 X := CFSG.SectionRank.pRank_coe_eq_openPRank 5 X
  have h2 : CFSG.Open.pRank 5 X ≤ CFSG.Open.pRank 5 M :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_mono 5 (by norm_num) (MinCex.le_M hX)
  have h3 : CFSG.Open.pRank 5 M ≤ CFSG.Assembly.RankThreeEven.localRank 5 G :=
    pRank_le_localRank_of_isTwoLocal (by norm_num) hM2
  have h4 : CFSG.Assembly.RankThreeEven.localRank 5 G < 3 :=
    hX.sec18H.toTheoremFourHyp.localRank_lt 5 (by norm_num) (by norm_num)
  omega

section Certified


theorem MinCex.normalizer_commutator_le (h1812 : Item181_2) (h184 : Item184_1) (h186 : Item186H)
    (hX : MinCex A M H c X) :
    Subgroup.normalizer ((⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  rw [commutator_pCoreOf_inf_eq h1812 hX.sec18H]
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hAH : A ≤ H := le_trans (le_trans le_sup_right le_sup_left) hX.sec18H.mem_scriptH.2.1.ge
  refine normalizer_le_of_le_normalizer h186 hX.sec18H hX.hyp187
    (commutator_ne_bot h184 h186 hX.sec18H hX.hyp187) ?_
    (le_normalizer_commutator h1812 hX.sec18H)
  refine Subgroup.commutator_le.mpr fun x hx z hz => ?_
  have hxH : x ∈ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hx
  have hzH : z ∈ H := (Subgroup.zpowers_le.mpr (hAH hcA)) hz
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hxH hzH) (inv_mem hxH)) (inv_mem hzH)

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
