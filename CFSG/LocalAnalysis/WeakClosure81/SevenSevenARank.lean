module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenA
public import CFSG.Milestones.ASVolI.I6
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.Blueprint.SourceExceptionalModels
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GH74.GLS.Defs
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsGrp
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsThree
public import CFSG.LocalAnalysis.WeakClosure81.TenFive
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ASVolI.ChIJK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem imageRankEqRank_iff {V A Y : Subgroup G} [(Y.subgroupOf A).Normal] {Q : Type} [Group Q]
    (ψ : ↥A →* Q) (hψ : Function.Surjective ψ) (hker : ∀ a : ↥A, ψ a = 1 ↔ (a : G) ∈ Y) :
    CFSG.ASVolI.ChIJK.ImageRankEqRank V A Y ↔
      CFSG.pRank 2 ↥((V.subgroupOf A).map ψ) = CFSG.pRank 2 Q := by
  have hker' : ψ.ker = Y.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker a
  let e : ↥A ⧸ (Y.subgroupOf A) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have he : ∀ a : ↥A, e (QuotientGroup.mk a) = ψ a := by
    intro a
    change (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
      ((QuotientGroup.quotientMulEquivOfEq hker'.symm) (QuotientGroup.mk a)) = ψ a
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk ψ a
  haveI : Finite (↥A ⧸ (Y.subgroupOf A)) :=
    Finite.of_surjective (QuotientGroup.mk' (Y.subgroupOf A))
      (QuotientGroup.mk'_surjective (Y.subgroupOf A))
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hquot : CFSG.pRank 2 (↥A ⧸ (Y.subgroupOf A)) = CFSG.pRank 2 Q :=
    CFSG.GH74.GLS.Bg.pRank_mulEquiv one_lt_two e
  have hcomp : ((e : ↥A ⧸ (Y.subgroupOf A) →* Q)).comp
      (QuotientGroup.mk' (Y.subgroupOf A)) = ψ :=
    MonoidHom.ext he
  have hSm : ((V.subgroupOf A).map (QuotientGroup.mk' (Y.subgroupOf A))).map
        (e : ↥A ⧸ (Y.subgroupOf A) →* Q) = (V.subgroupOf A).map ψ := by
    rw [Subgroup.map_map, hcomp]
  have hrankS : CFSG.pRank 2 ↥((V.subgroupOf A).map (QuotientGroup.mk' (Y.subgroupOf A))) =
      CFSG.pRank 2 ↥((V.subgroupOf A).map ψ) := by
    rw [← hSm]
    exact CFSG.GH74.GLS.Bg.pRank_mulEquiv one_lt_two
      (MulEquiv.subgroupMap e ((V.subgroupOf A).map (QuotientGroup.mk' (Y.subgroupOf A))))
  unfold CFSG.ASVolI.ChIJK.ImageRankEqRank
  rw [hquot, hrankS]

theorem isTISubgroup_of_isTI {V : Subgroup G} (hTI : IsTI V) :
    CFSG.ASVolI.ChIJK.IsTISubgroup V := by
  intro g hg
  rcases hTI g⁻¹ with hbot | heq
  · rwa [t75_conjSubgroup_eq, inv_inv] at hbot
  · exfalso
    apply hg
    have hle : V ≤ Quasithin.conjSubgroup V g := by
      rw [t75_conjSubgroup_eq, inv_inv] at heq
      exact le_of_eq_of_le heq.symm inf_le_right
    have hnormal : Quasithin.conjSubgroup V g = V :=
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_conjSubgroup' g V))).symm
    exact Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hnormal

private theorem seven_seven_rank_card_eq_two_pow {G : Type} [Group G] [Finite G]
    {W : Subgroup G} (hW : IsElemAbelian 2 W) :
    Nat.card W = 2 ^ CFSG.pRank 2 ↥W := by
  haveI : CFSG.IsElementaryAbelian 2 W :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hW
  obtain ⟨m, hm⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 W).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hm]
  exact hm

theorem pRank_image_eq_pRank_of_sup_conj (h : Hyp711 V H E) {k : G} (hk : k ∈ kSub V H E)
    (hne : ⁅V, conjSubgroup V k⁆ ≠ ⊥) {Q : Type} [Group Q]
    (ψ : ↥(V ⊔ conjSubgroup V k) →* Q) (hψ : Function.Surjective ψ)
    (hker : ∀ a : ↥(V ⊔ conjSubgroup V k),
      ψ a = 1 ↔ (a : G) ∈ pCoreOf 2 (V ⊔ conjSubgroup V k)) :
    CFSG.pRank 2 ↥((V.subgroupOf (V ⊔ conjSubgroup V k)).map ψ) = CFSG.pRank 2 Q := by
  have hA : IsElemAbelian 2 (conjSubgroup V k) := isElemAbelian_conjSubgroup' h.elemAbelian k
  have hTIV : CFSG.ASVolI.ChIJK.IsTISubgroup V := isTISubgroup_of_isTI h.ti
  have hTIA : CFSG.ASVolI.ChIJK.IsTISubgroup (conjSubgroup V k) :=
    isTISubgroup_of_isTI (isTI_conj h.ti k)
  have hcardV := seven_seven_rank_card_eq_two_pow h.elemAbelian
  have hcardA := seven_seven_rank_card_eq_two_pow hA
  have hcard : Nat.card V = Nat.card (conjSubgroup V k) := (card_conjSubgroup' k V).symm
  have hrank : CFSG.pRank 2 ↥V = CFSG.pRank 2 ↥(conjSubgroup V k) := by
    apply Nat.pow_right_injective (by norm_num : 1 < 2)
    change 2 ^ CFSG.pRank 2 ↥V = 2 ^ CFSG.pRank 2 ↥(conjSubgroup V k)
    rw [← hcardV, hcard, hcardA]
  have hne' : V ≠ conjSubgroup V k := by
    intro heq
    apply hne
    rw [← heq]
    exact Subgroup.commutator_self_eq_bot_iff.mpr h.elemAbelian.1
  have hcross : ∀ g : G, CFSG.conjugate (conjSubgroup V k) g ≠ V →
      CFSG.conjugate (conjSubgroup V k) g ⊓ V = ⊥ := by
    intro g hg
    have hconj : CFSG.conjugate (conjSubgroup V k) g = conjSubgroup V (k * g) := by
      change conjSubgroup (conjSubgroup V k) g = conjSubgroup V (k * g)
      rw [Quasithin.conjSubgroup_conjSubgroup]
    rw [hconj, inf_comm]
    rcases inf_conjSubgroup_eq_bot_or_eq h.ti 1 (k * g) with hbot | heq
    · rw [Quasithin.conjSubgroup_one] at hbot
      exact hbot
    · rw [Quasithin.conjSubgroup_one] at heq
      exact (hg (hconj.trans heq.symm)).elim
  have hkH : k ∈ H := kSub_le_of_forall_le h.omega_le hk
  have hAΩ : conjSubgroup V k ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem hkH
  have hNIn : NIn V (conjSubgroup V k) ≠ ⊥ := by
    obtain ⟨a, b, hVa, hVb, hNab⟩ :=
      nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian h.mem hAΩ
    show V ⊓ Subgroup.normalizer (conjSubgroup V k : Set G) ≠ ⊥
    have hEq : V ⊓ Subgroup.normalizer (conjSubgroup V k : Set G) =
        conjSubgroup V a ⊓ Subgroup.normalizer (conjSubgroup V b : Set G) := by
      rw [hVb]
      nth_rewrite 1 [hVa]
      rfl
    rw [hEq]
    exact hNab
  have hnotle := not_le_normalizer_conjSubgroup_of_commutator_ne_bot h.elemAbelian h.ti hne
  have hNIn_lt : NIn V (conjSubgroup V k) < V := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    apply hnotle
    have hle : NIn V (conjSubgroup V k) ≤ Subgroup.normalizer (conjSubgroup V k : Set G) :=
      inf_le_right
    rwa [hEq] at hle
  obtain ⟨hpart2a, hnormrank⟩ :=
    (CFSG.ASVolI.as_I_6_2 (G := G) V (conjSubgroup V k) h.elemAbelian hA hrank
      hTIV hTIA hne' hcross hNIn).2 hNIn_lt
  haveI hN : ((pairY V (conjSubgroup V k)).subgroupOf (V ⊔ conjSubgroup V k)).Normal :=
    hpart2a.2.1.2
  have hImage : CFSG.ASVolI.ChIJK.ImageRankEqRank V (V ⊔ conjSubgroup V k)
      (pairY V (conjSubgroup V k)) := hnormrank.1.2
  have hpair : pairY V (conjSubgroup V k) = pCoreOf 2 (V ⊔ conjSubgroup V k) :=
    (pCoreOf_sup_conj_eq_pairY h hk hne).symm
  have hker' : ∀ a : ↥(V ⊔ conjSubgroup V k), ψ a = 1 ↔ (a : G) ∈ pairY V (conjSubgroup V k) := by
    intro a
    rw [hker a, hpair]
  exact (imageRankEqRank_iff (Y := pairY V (conjSubgroup V k)) ψ hψ hker').mp hImage

end CFSG.LocalAnalysis.WeakClosure81
