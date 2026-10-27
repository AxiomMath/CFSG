module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (r1217_of_twelve_seventeen)

variable {G : Type} [Group G] [Finite G]

theorem barSub_ne_bot_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V) :
    barSub V₀ V c.ctx.hyp125.isElemAbelian L ≠ ⊥ := by
  set hV := c.ctx.hyp125.isElemAbelian with hVdef
  have h2 := h35.2 L n c.ctx c.v0
  have hU3 : IsU3 ↥(barSub V₀ V hV L) 2 := by
    have h := h2.1
    rwa [← h2.2.2.2] at h
  have hcard : Nat.card ↥(barSub V₀ V hV L) = 62400 := by
    have h := CFSG.Blueprint.LieModel.card_eq_lieOrd
      (X := ↥(barSub V₀ V hV L)) (t := .PSU) (n := 3) (p := 2) (f := 2)
      (by norm_num) hU3
    rw [h]
    decide
  intro hbot
  have h1 : Nat.card ↥(barSub V₀ V hV L) = 1 := by
    rw [hbot]
    simp
  omega

theorem barSub_subgroupOf_mbar_normal_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V) :
    ((barSub V₀ V c.ctx.hyp125.isElemAbelian L).subgroupOf
      (Mbar D.M V₀ V c.ctx.hyp125.isElemAbelian)).Normal := by
  have hL_eq : L = UC22.conjClosure D.M L := (h35.2 L n c.ctx c.v0).2.2.2
  have hLM : L ≤ D.M := c.ctx.mem_calC.1.le
  have hN : D.M ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL_eq]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.le_normalizer_conjClosure
      D.M L
  exact barSub_subgroupOf_mbar_normal c.ctx.hyp125.isElemAbelian hLM hN

theorem commSub_top_barSub_eq_top_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V c.ctx.hyp125.isElemAbelian))
      (barSub V₀ V c.ctx.hyp125.isElemAbelian L) = ⊤ := by
  classical
  set hV := c.ctx.hyp125.isElemAbelian with hVdef
  have hLbar_ne : barSub V₀ V hV L ≠ ⊥ := barSub_ne_bot_of_ctx17_40 c h35
  have hLbar_le : barSub V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.ctx.mem_calC.1.le
  have hLbar_normal : ((barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal_of_ctx17_40 c h35
  have hLbar_comp : barSub V₀ V hV L ∈ compBar D.M V₀ V hV :=
    barSub_mem_compBar_of_ne_bot c.ctx.hyp125 c.ctx.mem_calC hLbar_ne
  have hsup : barSub V₀ V hV L =
      ⨆ (φ : MulAut (Vtil V₀ V hV)) (_ : φ ∈ Mbar D.M V₀ V hV),
        (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom := by
    apply le_antisymm
    · intro x hx
      exact Subgroup.mem_iSup_of_mem (1 : MulAut (Vtil V₀ V hV))
        (Subgroup.mem_iSup_of_mem (Subgroup.one_mem _)
          (show x ∈ (barSub V₀ V hV L).map
              (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom from
            ⟨x, hx, by simp [MulAut.conj_apply]⟩))
    · refine iSup₂_le fun φ hφ => ?_
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      have hnorm : Mbar D.M V₀ V hV ≤
          Subgroup.normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLbar_le).mp hLbar_normal
      have hconj : φ * l * φ⁻¹ ∈ barSub V₀ V hV L :=
        (Subgroup.mem_normalizer_iff.mp (hnorm hφ) l).mp hl
      simpa [MulAut.conj_apply] using hconj
  have hdisj : Odd (Nat.card (barSub V₀ V hV L)) ∨
      ∃ K ∈ compBar D.M V₀ V hV,
        barSub V₀ V hV L =
          ⨆ (φ : MulAut (Vtil V₀ V hV)) (_ : φ ∈ Mbar D.M V₀ V hV),
            K.map (MulAut.conj φ).toMonoidHom :=
    Or.inr ⟨barSub V₀ V hV L, hLbar_comp, hsup⟩
  have hIrr : ⨆ I ∈ irrSet (barSub V₀ V hV L), I = ⊤ :=
    r1217_of_twelve_seventeen D hx h61 h127 h1214
      V₀ V c.ctx.hyp125 (barSub V₀ V hV L) hLbar_ne hLbar_le hLbar_normal hdisj
  rw [eq_top_iff]
  calc (⊤ : Subgroup (Vtil V₀ V hV))
      = ⨆ I ∈ irrSet (barSub V₀ V hV L), I := hIrr.symm
    _ ≤ CFSG.Quasithin.commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) := by
        refine iSup₂_le fun I hI => ?_
        rw [← hI.1]
        exact CFSG.Quasithin.commSub_mono le_top le_rfl

theorem cNatModSU3_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    CNatModSU3 (Vtil V₀ V c.ctx.hyp125.isElemAbelian)
      (barSub V₀ V c.ctx.hyp125.isElemAbelian L) n := by
  have h := (h35.1 L n c.ctx).1
  rw [commSub_top_barSub_eq_top_of_ctx17_40 c h35 hx h61 h127 h1214] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
