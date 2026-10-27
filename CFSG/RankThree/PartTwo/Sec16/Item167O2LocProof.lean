module

public import CFSG.RankThree.PartTwo.Sec16.Item167O2LocLift
public import CFSG.RankThree.PartTwo.Sec16.Item166Res2Proof167
public import CFSG.RankThree.PartTwo.Sec4.Item41ScopeProofAll
import CFSG.RankThree.PartTwo.Sec16.Item167O2LocCore
import CFSG.RankThree.PartTwo.Sec16.Item167O2LocFour
import CFSG.RankThree.PartTwo.Sec16.Item167O2LocEnd
import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofCompOne

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {A : Subgroup G} {c : G} {L : Subgroup G}

namespace Proof167O2Loc

theorem step167O2Loc_of_not
    (h : Sec15R G A c L) (h163 : Item163 A (lB A) c L)
    (h153 : Item153Main A (lB A)) (hL : ¬ IsL3TwoPow L) :
    Step167O2Loc A (lB A) c L := by
  intro Y hY hH hF Y₀ hY₀ hZ1 hZA hY₀Z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := pPrimeCoreOf 2 Y with hZdef
  set N := Subgroup.normalizer (Z : Set G) with hNdef
  have hZle : Z ≤ Y := pPrimeCoreOf_le 2 Y
  have hYN : Y ≤ N := le_normalizer_pPrimeCoreOf 2 Y
  have hAN : A ≤ N := hZA.trans (Subgroup.centralizer_le_normalizer _)
  have hY₀N : Y₀ ≤ N := hY₀Z.trans (Subgroup.centralizer_le_normalizer _)
  have hLY₀ : L ≤ Y₀ := (h163 Y₀ hY₀).2.2.2.1
  have hLN : L ≤ N := hLY₀.trans hY₀N
  have hYne : Y ≠ ⊤ := hY.prop.1.1.1.1
  have hNne : N ≠ ⊤ := by
    intro htop
    have hZnormal : Z.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases h.isSimpleGroup.eq_bot_or_eq_top_of_normal Z with hbot | htop'
    · exact hZ1 hbot
    · exact hYne (top_le_iff.mp (htop' ▸ hZle))
  have hNmem : N ∈ scriptY A :=
    ⟨hNne, fun a ha => Subgroup.le_normalizer (hAN ha)⟩
  have hY₀NN : Y₀ ≤ Subgroup.normalizer (N : Set G) :=
    fun y hy => Subgroup.le_normalizer (hY₀N hy)
  obtain ⟨J, hJ, hLJ, hY₀J, hAJ, hQJ⟩ :=
    Proof167Core.exists_thetaComponent_of_scriptY0 h.toSec14Std hNne hAN hLN hY₀.prop hLY₀ hY₀NN
  have hYJ : Y ≤ Subgroup.normalizer (J : Set G) :=
    Proof167Core.le_normalizer_of_oPrimeResidualOf_eq_bot hQJ
      (fun y hy => Subgroup.le_normalizer (hYN hy)) hY.prop.1.1.1.2 hY.prop.2
  have hJN : J ≤ N := le_of_mem_thetaComponentsIn hJ
  have hJtop : J ≠ ⊤ := by
    intro hJt
    exact hNne (top_le_iff.mp (hJt ▸ hJN))
  letI : (Sec14.ker148 A N).Normal := Sec14.ker148_normal hNmem.2
  by_cases hO2 : CFSG.pCore 2 ↥J = ⊥
  · exfalso
    have h3L : 3 ∣ Nat.card L := Proof1613.three_dvd_card_L h.toSec14Std
    have h3J : 3 ∣ Nat.card J := h3L.trans (Subgroup.card_dvd_of_le hLJ)
    have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJ
    have hS4 : SectionFourHyp ↥J := h.toTheoremFourHyp.sectionFourHyp hJtop
    have h44 : Sec4.Item4_4 := Sec4.Census.rank3II_4_4_of_griess_noItem41
    have hLsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      isSimpleGroup_lBar_of_sec15R h
    have hLnotsmall : ¬ Proof167Four.Small44
        (Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
      refine Proof167Four.not_small44_card _ ?_ ?_
      · rcases (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with
          h1 | h2 | h3 | h4 | h5
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
      · intro n hn hiso
        exact hL ⟨n, hn, hiso⟩
    have hY₀q : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := hY₀.prop.1.2.2.2
    have hY₀F : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀ := (h153 Y₀ hY₀).2.2
    have hlift := Proof167Core.lift429_of (A := A) (c := c) (L := L) (N := N) (J := J)
      h.toSec14Std hNmem hAN hLN hJ hLJ hAJ
    rcases hlift with heq | halt | hL3
    · have hXM : J ≤ N ⊔ A := by
        rwa [sup_eq_left.mpr hAN]
      have hJsupL : J = L ⊔ inSubgroup (aschbacherSolvableCore 3) J :=
        Desc143X.eq_sup_theta_of_img148_eq (A := A) (Y := N) (X := J) (T := L)
          hJ h3J hXM hLJ heq
      let eQ := Item87Res2Proof.quotEquivOfImageEqTop hLJ
        (Item87Proof.imageModTheta_eq_top_of_eq_sup hLJ hJsupL)
      have hJsimple : IsSimpleGroup (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
        eQ.symm.isSimpleGroup
      have hJnotsmall : ¬ Proof167Four.Small44
          (Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J)) := by
        have hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) =
            Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
          Nat.card_congr eQ.toEquiv
        rwa [hcard] at hLnotsmall
      have hcomm := Proof167Four.commutator_theta_le_oddCore_or_small44 h44 hS4 hJp hJsimple hO2
      rcases hcomm with hc | hsmall
      · have hJeq : J = Y₀ ⊔ inSubgroup (aschbacherSolvableCore 3) J :=
          Proof167End.eq_sup_theta_of_img148_eq hAN hJ h3J hLY₀ hY₀J heq
        have hθ := Proof167End.pCore_le_theta_of_eq_sup hY₀J hJsimple hJp hJeq
        exact Proof167End.false_of_pCore_le_theta hY₀q hY₀F hY₀J hθ hc
      · exact absurd hsmall hJnotsmall
    · obtain ⟨h7, h10⟩ := halt
      obtain ⟨eJθ⟩ :=
        Desc143X.nonempty_quotTheta_equiv_img148 (A := A) (Y := N) hJ h3J
      let e : (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃* alternatingGroup (Fin 10) :=
        eJθ.trans h10.some
      have hJsimple : IsSimpleGroup (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
        haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
          alternatingGroup.isSimpleGroup (by simp)
        exact e.isSimpleGroup
      have hJnotsmall : ¬ Proof167Four.Small44
          (Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J)) := by
        have hcard : Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) = 1814400 := by
          rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2]
        rw [hcard]
        exact Proof167Four.not_small44_of_eq (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      have hcomm := Proof167Four.commutator_theta_le_oddCore_or_small44 h44 hS4 hJp hJsimple hO2
      rcases hcomm with hc | hsmall
      · have hθ := Proof167End.pCore_le_theta_of_alt hAN hJ h3J hLY₀ hY₀J h7 h10
        exact Proof167End.false_of_pCore_le_theta hY₀q hY₀F hY₀J hθ hc
      · exact absurd hsmall hJnotsmall
    · exact absurd hL3 hL
  · refine ⟨CFSG.Open.pCoreOf 2 J, pCoreOf_ne_bot_of_pCore_ne_bot hO2,
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J, ?_⟩
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hAJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
    · exact hY₀J.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
    · exact hYJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)

end Proof167O2Loc

theorem step167O2LocNot2nR_of
    (h163 : Item163R) (h153 : Item153MainR) :
    Step167O2LocNot2nR :=
  fun G _ _ A c L h hL =>
    Proof167O2Loc.step167O2Loc_of_not h (h163 G A c L h) (h153 G A c L h) hL

end CFSG.RankThree.PartTwo.Sec16
