module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroup
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PShape
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroupJ
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

theorem cases148_of_not_le
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h149 : Item149 A (lB A))
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    [(ker148 A M).Normal] (hWO : ¬ w155 A M X ≤ pPrimeCoreOf 3 M) :
    ∃ d : G, d ∈ A ∧ d ≠ 1 ∧ (∀ w ∈ w155 A M X, ⁅w, d⁆ ∈ pPrimeCoreOf 3 M) ∧
      5 ∣ Nat.card X ∧
      (Nonempty (↥(img148 A M (w155 A M X)) ≃* alternatingGroup (Fin 5)) ∨
        (Sec4.IsTripleCover ↥(img148 A M (w155 A M X)) (alternatingGroup (Fin 6)) ∧
          CFSG.IsQuasisimple ↥(img148 A M (w155 A M X)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (ker148 A M).Normal := ker148_normal hf.mem_m2.1.2
  set W := w155 A M X with hWdef
  set D := img148 A M (deltaZero A (lB A) M) with hDdef
  have hWΔ : W ≤ deltaZero A (lB A) M := hf.w_le_i0.trans hf.i0_le_deltaZero
  have hXΔ : X ≤ deltaZero A (lB A) M := hf.le_x_i0.trans hf.i0_le_deltaZero
  have hWM : W ≤ M := hWΔ.trans (deltaZero_le M)
  have hAM : A ≤ M := hf.le_am
  have hXMA : X ≤ M ⊔ A := hf.le_xm.trans le_sup_left
  have hWMA : W ≤ M ⊔ A := hWM.trans le_sup_left
  have hΔMA : deltaZero A (lB A) M ≤ M ⊔ A := (deltaZero_le M).trans le_sup_left
  set V := (img148 A M X).subgroupOf D with hVdef
  set E := (img148 A M W).subgroupOf D with hEdef
  have hEimg : img148 A M W ≤ D := by rw [hDdef]; exact img148_mono hWΔ
  have hVsub : V.IsSubnormal := by
    rw [hVdef, hDdef]
    exact Proof153Twin3.isSubnormal_img_subgroupOf hAM hX
  obtain ⟨eX⟩ := Proof155INorm.nonempty_quot_equiv_img (A := A) (M := M)
    (D := deltaZero A (lB A) M) hAM hX hXΔ
  have hVq : CFSG.IsQuasisimple ↥V :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX (Proof1515.isQuasisimple_quot_pPrimeCore hf.mem_x4)
  have hEperf : Group.IsPerfect ↥E := by
    rw [hEdef]
    haveI : Group.IsPerfect ↥(img148 A M W) := by
      haveI : Group.IsPerfect W := Proof155Wx.isPerfect_w155 A M X
      exact isPerfect_img148 (A := A) (Y := M) (J := W) hWMA
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hEimg).symm.toMonoidHom) (MulEquiv.surjective _)
  have hWne : img148 A M W ≠ ⊥ := img148_ne_bot_of_not_le hWM hWO
  have hEne : E ≠ ⊥ := by
    rw [hEdef]
    intro hbot
    apply hWne
    have h := congrArg (Subgroup.map D.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hEimg, Subgroup.map_bot] at h
  have hEsub : E.IsSubnormal := by
    rw [hEdef]
    have hMA : M = M ⊔ A := (sup_eq_left.mpr hAM).symm
    have h2 : (W.subgroupOf (M ⊔ A)).IsSubnormal := by
      rw [← hMA]
      exact CFSG.Open.IsSubnormal.subgroupOf hf.subnormal_w_m
    have h3 : (img148 A M W).IsSubnormal := by
      have h := Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective (ker148 A M)) h2
      simpa [img148] using h
    exact h3.subgroupOf
  have hcomm : ⁅X, W⁆ ≤ pPrimeCoreOf 3 M := by
    rw [hWdef, Subgroup.commutator_comm]
    exact (commutator_w155_le hf hX).trans
      (CFSG.RankThree.PartTwo.Sec17.Proof17Q0.pCoreOf_le_pPrimeCoreOf M)
  have hVE : ⁅V, E⁆ = ⊥ := by
    rw [hVdef, hEdef, hDdef]
    exact Proof153Twin3.commutator_img_subgroupOf_eq_bot (D := deltaZero A (lB A) M)
      hXΔ hWΔ hΔMA hcomm
  have hshape := shape148_of_ne_bot (A := A) (L := L) (c := c) h h148 hf.mem_m2 V E
    hVsub hVq hEperf hVE hEne
  rcases hshape with ⟨d, hdA, hd1, hdec, hT⟩ | ⟨eJ2⟩
  ·
    haveI : Group.IsPerfect ↥D := by
      rw [hDdef]
      exact Read148Perf.isPerfect_img148 h h148 hf.mem_m2.1
    have hrank : ∀ F : Subgroup ↥D, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27 := by
      intro F hF
      have hF' : CFSG.Assembly.IsElemAbelian 3 (F.map D.subtype) :=
        CFSG.Open.IsElemAbelian.map hF D.subtype
      have h := Proof15Res8Prod.card_le_of_isElemAbelian_img148 (A := A) (M := M) h
        hf.mem_m2.1.2 hf.mem_m2.2 hF'
      rwa [Subgroup.card_map_of_injective D.subtype_injective] at h
    obtain ⟨h5V, hEtype, hNtriv⟩ := prod148_facts hrank hT hVsub hVq hEsub hEperf hEne hVE
    refine ⟨d, hdA, hd1, ?_, ?_, ?_⟩
    ·
      intro w hw
      exact commutator_mem_of_dec (LB := lB A) hdec
        (pPrimeCoreOf_deltaZero_le (LB := lB A) hNtriv)
        (le_normalizer_pPrimeCoreOf 3 M (hAM hdA)) w (hWΔ hw)
    ·
      have hcardV : Nat.card V = Nat.card (img148 A M X) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (img148_mono hXΔ)).toEquiv
      exact (hcardV ▸ h5V).trans (Main148.card_img148_dvd hXMA)
    ·
      rcases hEtype with hE5 | hE6
      · obtain ⟨φ⟩ := hE5
        exact Or.inl ⟨(Subgroup.subgroupOfEquivOfLe hEimg).symm.trans φ⟩
      · obtain ⟨htc, hq⟩ := hE6
        exact Or.inr ⟨Proof15Res8Diag.isTripleCover_congr
          (Subgroup.subgroupOfEquivOfLe hEimg) htc,
          CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEimg) hq⟩
  ·
    exfalso
    obtain ⟨eJ2⟩ := eJ2
    have hcase := j2prod_facts (T := ↥D) eJ2 hVsub hVq hEsub hEperf hEne hVE
    have hcardE : Nat.card E = Nat.card (img148 A M W) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEimg).toEquiv
    have hcardV : Nat.card V = Nat.card (img148 A M X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (img148_mono hXΔ)).toEquiv
    rcases hcase with ⟨hVrank, h5E⟩ | ⟨h5V, hErank⟩
    ·
      have h5W : 5 ∣ Nat.card W :=
        (hcardE ▸ h5E).trans (Main148.card_img148_dvd hWMA)
      have hXle : CFSG.Open.pRank 5 X ≤ 1 := pRank_five_x_le_one h hf hX h5W
      have h2q : 2 ≤ CFSG.Open.pRank 5
          (⊤ : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5) eX]
        exact hVrank
      have h2X : 2 ≤ CFSG.Open.pRank 5 X := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
        exact CFSG.GroupTheory.two_le_pRank_of_quotient (CFSG.pPrimeCore 3 ↥X) (by norm_num)
          (by norm_num) h2q
      omega
    ·
      have h5X : 5 ∣ Nat.card X :=
        (hcardV ▸ h5V).trans (Main148.card_img148_dvd hXMA)
      have hWle : CFSG.Open.pRank 5 W ≤ 1 := pRank_five_w155_le_one h hf hX h5X
      have h2img : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(img148 A M W)) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5)
          (Subgroup.subgroupOfEquivOfLe hEimg)]
        exact hErank
      have h2W : 2 ≤ CFSG.Open.pRank 5 W := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup W]
        let f : ↥(W.subgroupOf (M ⊔ A)) →* ↥(img148 A M W) :=
          ((QuotientGroup.mk' (ker148 A M)).comp (W.subgroupOf (M ⊔ A)).subtype).codRestrict
            (img148 A M W) (fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
        have hfsurj : Function.Surjective f := by
          intro y
          obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp y.2
          exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
        let g : ↥W →* ↥(img148 A M W) :=
          f.comp (Subgroup.subgroupOfEquivOfLe hWMA).symm.toMonoidHom
        have h2q : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (↥W ⧸ g.ker)) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5)
            (QuotientGroup.quotientKerEquivOfSurjective g (hfsurj.comp (MulEquiv.surjective _)))]
          exact h2img
        exact CFSG.GroupTheory.two_le_pRank_of_quotient g.ker (by norm_num) (by norm_num) h2q
      omega

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
