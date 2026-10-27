module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofOmega
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofK
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofE
public import CFSG.RankThree.PartTwo.Sec12.Item12ResProofThree
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
public import CFSG.RankThree.PartTwo.Sec13.Item131Assembly

public section

namespace CFSG.RankThree.PartTwo.Sec13.Item131bProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem normalizer_le_of_heis_three (h125 : Sec12.Item125BarThree) (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hty : HeisType (L ⧸ aschbacherSolvableCore 3 L)) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hcL := mem_of_isHeisCentral hD hH
  have hZ3 := card_center_eq_three hty
  obtain ⟨U, hzU, hU9, hU3, hUΛ, hUΛz, hAbU⟩ := exists_U_of_isHeisCentral hD hcL hH hZ3
  obtain ⟨E, hEle, hEe, hE27, hEC, hEL, hAN⟩ :=
    exists_E_of_U hD hcL hzU hU9 hU3 hUΛ hUΛz hAbU
  obtain ⟨hcE, hC9, -, hsup⟩ := e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hstd := sec12StdBar_of_heis hD hcL hEe hE27 hcE hC9 hsup hAN
  have hB3 : Nat.card (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3 := by
    rw [inf_thetaQuotCentralizer_eq hD, hD.card_zpowers]
  have hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
    have heq : A ⊓ L = Subgroup.zpowers c :=
      le_antisymm (inf_le_zpowers hD hH hcL hZ3)
        (Subgroup.zpowers_le.mpr ⟨hD.mem_A, hcL⟩)
    rw [heq, hD.card_zpowers]
  exact h125 G E c L hstd (type122_of hty) A ⟨hD.isElemAbelian, hD.card_eq⟩ (le_lcBar hD hH)
    hD.mem_A hB3 hAL3

end CFSG.RankThree.PartTwo.Sec13.Item131bProof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item131bProof

theorem item131b_of_three
    (h125 : Sec12.Item125BarThree) (h128 : Sec12.Item128BarAt) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hSL : Step131bSLTwo) : Item131b := by
  have hHE := step131bHeisE h128 h422 h45
  have hHK := step131bHeisK h45
  intro G _ _ A c L hD hcase
  rcases hcase with hSL2 | ⟨hH, hty⟩
  ·
    have hFE : partTwoF G = partTwoE G :=
      (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
    have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hq.1
    have : IsSimpleGroup ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := hq.2.1
    have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) :=
      (QuotientGroup.mk_surjective
        (s := Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))).nontrivial
    refine ⟨fun hH => (not_isHeisCentral_of_isSLThreePiTwo hSL2 hH).elim,
      fun E hEle hEe hE27 hEC hEL => ?_⟩
    have hET := hSL G A c L hD hSL2 E hEle hEe hE27 hEC hEL
    exact ⟨hFE ▸ hET.1, fun h => (h hET).elim⟩
  ·
    exact ⟨fun _ => normalizer_le_of_heis_three h125 hD hH hty,
      fun E hEle hEe hE27 hEC hEL =>
        clauses_of_heis h128 h422 h45 hHE hHK hD hH hty hEle hEe hE27 hEC hEL⟩

theorem item131b_of_item45
    (h128 : Sec12.Item128BarAt) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hSL : Step131bSLTwo) : Item131b :=
  item131b_of_three (Sec12.item125BarThree_of_item45' h45) h128 h422 h45 hSL

end CFSG.RankThree.PartTwo.Sec13
