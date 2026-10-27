module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_exists_not_mem_nBar (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.isElemAbelian L) :
    ∃ x ∈ D.M, x ∉ nBar D.M V₀ V h.isElemAbelian L := by
  by_contra hno
  push Not at hno
  have hV := h.isElemAbelian
  have hset : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} =
      {barSub V₀ V hV L} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨g, hgM, hg⟩ := (mem_barSub V₀ V hV D.M φ⁻¹).1 ((Mbar D.M V₀ V hV).inv_mem hφ)
      have hmem := (s15_Infra_mem_nBar_iff h.hyp125 hV hgM).1 (hno g hgM)
      rw [s15_Infra_barSub_conjSubgroup V₀ V hV g.2 L, hg, inv_inv] at hmem
      exact hmem
    · rintro rfl
      exact ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext x; simp⟩
  have h1 : s15 D.M V₀ V hV L = 1 := by
    unfold s15
    rw [hset, Set.ncard_singleton]
  omega

theorem s16c34_preBarSub_le_cElt {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} {y : IntMod V hV}
    (hfix : mkTil V₀ V hV y ∈ fixV K) :
    preBarSub M V₀ V hV K ≤ F11.CElt M V₀ y.val := by
  intro g hg
  obtain ⟨hgM, hgs, hK⟩ := (mem_preBarSub M V₀ V hV K).1 hg
  refine ⟨hgM, stabTil_le_normalizer₀ V₀ V hgs, ?_⟩
  have h1 := (mem_fixV.mp hfix) (actTil V₀ V hV ⟨g, hgs⟩) hK
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
  exact h1

theorem s16c34_preBarSub_le_cElt_v1 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {c : G} (hc : c ∈ D.M) {w : G} (hw : w ∈ v1Sub D.M V₀ V h.isElemAbelian L) :
    preBarSub D.M V₀ V h.isElemAbelian
        (barSub V₀ V h.isElemAbelian (conjSubgroup L c)) ≤ F11.CElt D.M V₀ w := by
  have hV := h.isElemAbelian
  have hwV : w ∈ V := s15_Infra_v1Sub_le h.hyp125 hV hw
  have hfix : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      fixV (barSub V₀ V hV (conjSubgroup L c)) :=
    s15_Core_imgTil_v1Sub_le_fixV h hc
      ((mem_imgTil V₀ V hV _ _).2 ⟨IntMod.mk hV ⟨w, hwV⟩, hw, rfl⟩)
  exact s16c34_preBarSub_le_cElt hV hfix

theorem s16c34_delta_lt_gamma_of_ne_bot (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (h0 : V₀ ≠ ⊥)
    (hγ : 4 ≤ gamma15 D.M V₀ V h.hyp151.isElemAbelian L) :
    delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1 := by
  have hδ : delta15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 2 := by
    unfold delta15
    rw [v1Sub_of_ne_bot D.M V₀ V _ L h0]
    exact (rk_mono inf_le_left).trans h.hyp16.small
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
