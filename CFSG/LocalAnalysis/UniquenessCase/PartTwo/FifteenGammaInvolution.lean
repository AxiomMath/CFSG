module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rank
public import CFSG.GroupTheory.E3Params
public import CFSG.Quasithin.EmptyFaithful.S146zUG1Core
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commSub_le_fixV_of_commutator_eq_bot {W : Type*} [CommGroup W]
    {A B : Subgroup (MulAut W)} (hAB : ⁅A, B⁆ = ⊥) (hA : commSub ⊤ A ≤ fixV B) :
    commSub ⊤ B ≤ fixV A := by
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨b, hb, v, -, rfl⟩
  refine mem_fixV.mpr fun a ha => ?_
  refine CFSG.Quasithin.S146zU.UG1.fix_swap (a := b) (b := a) ?_ ?_ v
  · have hmem : ⁅b, a⁆ ∈ ⁅A, B⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb ha
    rw [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · intro y
    exact mem_fixV.mp (hA (Subgroup.subset_closure ⟨a, ha, y, Subgroup.mem_top y, rfl⟩)) b hb

theorem s15_Gamma_wTil_sup_fixV_eq_top (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {t : MulAut (Vtil V₀ V h.isElemAbelian)} (htL : t ∈ barSub V₀ V h.isElemAbelian L) :
    wTil V₀ V h.isElemAbelian L ⊔ fixV (Subgroup.zpowers t) = ⊤ := by
  have hV := h.isElemAbelian
  have hzip : Subgroup.zpowers t ≤ barSub V₀ V hV L := Subgroup.zpowers_le.mpr htL
  have hval : ∀ g : D.M, commSub ⊤ (barSub V₀ V hV (conjSubgroup L (g : G))) ≤
      wTil V₀ V hV L ⊔ fixV (Subgroup.zpowers t) := by
    intro g
    by_cases hgn : (g : G) ∈ nBar D.M V₀ V hV L
    · have hK : barSub V₀ V hV (conjSubgroup L (g : G)) = barSub V₀ V hV L :=
        (s15_Infra_mem_nBar_iff h.hyp125 hV g.2).1 hgn
      rw [hK]
      exact le_sup_left
    · have hcomm := h.commute (g : G) g.2 hgn
      have hswap : commSub ⊤ (barSub V₀ V hV (conjSubgroup L (g : G))) ≤
          fixV (barSub V₀ V hV L) :=
        commSub_le_fixV_of_commutator_eq_bot hcomm.1
          (by simpa only [wTil] using commSub_eq_bot_iff.mp hcomm.2)
      exact hswap.trans ((fixV_anti hzip).trans le_sup_right)
  have htop := s15_Two_iSup_commSub_eq_top D h1217 h hL
  refine le_antisymm le_top ?_
  rw [← htop]
  exact iSup_le hval

theorem mBar_le_gamma15_of_R1217 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {t : MulAut (Vtil V₀ V h.isElemAbelian)} (htL : t ∈ barSub V₀ V h.isElemAbelian L)
    (hto : orderOf t = 2) :
    mBar D.M V₀ V h.isElemAbelian ≤ gamma15 D.M V₀ V h.isElemAbelian L := by
  have hV := h.isElemAbelian
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto]; norm_num)
  have hzple : Subgroup.zpowers t ≤ Mbar D.M V₀ V hV :=
    (Subgroup.zpowers_le.mpr htL).trans (barSub_mono V₀ V hV h.le)
  have hzpne : Subgroup.zpowers t ≠ ⊥ := by
    intro hbot
    have ht1 : t = 1 := by
      have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [ht1] at hto
    simp at hto
  set T : Subgroup (Vtil V₀ V hV) := fixV (Subgroup.zpowers t) with hT
  have hmbar : mBar D.M V₀ V hV ≤ E3.mQuot (⊤ : Subgroup (Vtil V₀ V hV)) T := by
    have h := E3.mParam_le_rkIdx_fixV hzple hzp hzpne
    simpa only [mBar, hT, CFSG.GroupTheory.mQuot_top_eq_rkIdx] using h
  have hsplit_top : wTil V₀ V hV L ⊔ T = ⊤ := by
    have h := s15_Gamma_wTil_sup_fixV_eq_top D h1217 h hL htL
    simpa only [hT] using h
  have hquot : E3.mQuot (⊤ : Subgroup (Vtil V₀ V hV)) T =
      E3.mQuot (wTil V₀ V hV L) (wTil V₀ V hV L ⊓ T) := by
    have hsplit : E3.mQuot (wTil V₀ V hV L ⊔ T) T =
        E3.mQuot (wTil V₀ V hV L) (wTil V₀ V hV L ⊓ T) := by
      unfold E3.mQuot
      have h1 : T.relIndex (wTil V₀ V hV L ⊔ T) = T.relIndex (wTil V₀ V hV L) :=
        Subgroup.relIndex_sup_right (wTil V₀ V hV L) T
      have h2 : T.relIndex (wTil V₀ V hV L) =
          (wTil V₀ V hV L ⊓ T).relIndex (wTil V₀ V hV L) := by
        rw [← Subgroup.inf_relIndex_right (H := T) (K := wTil V₀ V hV L),
          inf_comm T (wTil V₀ V hV L)]
      rw [h1, h2]
    rwa [hsplit_top] at hsplit
  have hmono : wTil V₀ V hV L ⊓ fixV (barSub V₀ V hV L) ≤ wTil V₀ V hV L ⊓ T := by
    refine inf_le_inf_left _ ?_
    rw [hT]
    exact fixV_anti (Subgroup.zpowers_le.mpr htL)
  calc mBar D.M V₀ V hV ≤ E3.mQuot (⊤ : Subgroup (Vtil V₀ V hV)) T := hmbar
    _ = E3.mQuot (wTil V₀ V hV L) (wTil V₀ V hV L ⊓ T) := hquot
    _ ≤ E3.mQuot (wTil V₀ V hV L) (wTil V₀ V hV L ⊓ fixV (barSub V₀ V hV L)) :=
        E3.mQuot_mono hmono
    _ ≤ gamma15 D.M V₀ V hV L := c8_mQuot_wTil_le_gamma15 D h hV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
