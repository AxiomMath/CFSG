module

public import CFSG.RankThree.PartTwo.Sec15.F153Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem sup_ne_top_of_pCoreOf_ne_bot (h : TheoremFourHyp G) {Y S : Subgroup G}
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥) :
    Y ⊔ S ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := h.isSimpleGroup
  have hle : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 (Y ⊔ S) := by
    rw [← Push153.inf_pCoreOf_sup_eq hSY]
    exact inf_le_right
  have hne : CFSG.Open.pCoreOf 2 (Y ⊔ S) ≠ ⊥ := fun h0 => hO2 (le_bot_iff.mp (h0 ▸ hle))
  have hn : (CFSG.Open.pCoreOf 2 (Y ⊔ S)).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← htop]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQtop : CFSG.Open.pCoreOf 2 (Y ⊔ S) = ⊤ := hn.eq_bot_or_eq_top.resolve_left hne
  have hP : IsPGroup 2 G := by
    have h1 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Y ⊔ S)
    rw [hQtop] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hcn : Nontrivial (Subgroup.center G) := hP.center_nontrivial
  have hc : Subgroup.center G = ⊤ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h0 | h1
    · exact absurd h0 ((Subgroup.nontrivial_iff_ne_bot _).mp hcn)
    · exact h1
  obtain ⟨a, b, hab⟩ := h.nonabelian
  exact hab ((Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top a) b).symm)

theorem concl153Push_of_noFFModule (h149 : Sec16.Item149S14) (htwin : Claim153TwinR)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hno : ¬ CharNormal153 Y S) (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    {T : Type} [Group T] (hT : NoFFModule T)
    (e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* T) :
    Concl153Push A Y S := by
  exfalso
  have hh := hR.toSec14Std
  have hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y :=
    Push153.generalizedFitting_eq_of_mem_scriptY0Star hh (h149 G A c L hh) (htwin G A c L hR) hY
  have hY3 : Y = oPrimeResidualOf 3 Y := hY.prop.1.2.1
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
  have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
    hKP.isKGroup (Y ⊔ S) (sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hO2)
  exact leaf_false_of_noFFModule hKH hF hY3 hYq hS2 hSY hFF hno hT e

theorem nonempty_centerQuotient_equiv_of_simple {Q T : Type} [Group Q] [Group T]
    (hq : CFSG.IsQuasisimple Q) (hT : IsSimpleGroup T) (e : Q ≃* T) :
    Nonempty (Q ⧸ Subgroup.center Q ≃* T) := by
  haveI := hT
  have hQs : IsSimpleGroup Q := e.isSimpleGroup
  have hnab : ∃ a b : Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hc : Subgroup.center Q = ⊥ := CFSG.RankThree.PartTwo.Sec15.center_eq_bot_of_isSimpleGroup hQs hnab
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩

end CFSG.RankThree.PartTwo.Sec15.F153
