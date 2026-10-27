module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_wTil_sup_conj_eq_top_of_setting16
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    wTil ⊥ V h.hyp151.isElemAbelian L ⊔
        wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) = ⊤ := by
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  refine le_antisymm le_top ?_
  rw [← hW.1]
  refine iSup₂_le fun X hX => ?_
  rcases hX with ⟨φ, hφ, rfl⟩
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub ⊥ V hV D.M φ).1 hφ
  rw [← hgφ]
  have hg_inv : (g : G)⁻¹ ∈ stabTil ⊥ V := (stabTil ⊥ V).inv_mem g.2
  have hα : (actTil ⊥ V hV) ⟨(g : G)⁻¹, hg_inv⟩ = ((actTil ⊥ V hV) g)⁻¹ := by
    rw [show (⟨(g : G)⁻¹, hg_inv⟩ : stabTil ⊥ V) = g⁻¹ from Subtype.ext rfl, map_inv]
  have hbar : (barSub ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV g)).toMonoidHom
      = barSub ⊥ V hV (conjSubgroup L (g : G)⁻¹) := by
    have hconj : MulAut.conj (actTil ⊥ V hV g)
        = MulAut.conj ((actTil ⊥ V hV) ⟨(g : G)⁻¹, hg_inv⟩)⁻¹ := by
      rw [hα, inv_inv]
    rw [hconj, ← s15_Infra_barSub_conjSubgroup ⊥ V hV hg_inv L]
  have hmap : (wTil ⊥ V hV L).map (actTil ⊥ V hV g).toMonoidHom
      = commSub ⊤ (barSub ⊥ V hV (conjSubgroup L (g : G)⁻¹)) := by
    rw [show wTil ⊥ V hV L = commSub ⊤ (barSub ⊥ V hV L) from rfl]
    rw [← s15_Infra_commSub_top_map_conj (barSub ⊥ V hV L) (actTil ⊥ V hV g), hbar]
  change (wTil ⊥ V hV L).map (actTil ⊥ V hV g).toMonoidHom ≤
    wTil ⊥ V hV L ⊔ wTil ⊥ V hV (conjSubgroup L x)
  rw [hmap]
  change wTil ⊥ V hV (conjSubgroup L (g : G)⁻¹) ≤
    wTil ⊥ V hV L ⊔ wTil ⊥ V hV (conjSubgroup L x)
  rcases c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn (m := (g : G)⁻¹)
      (D.M.inv_mem hgM) with hc | hc
  · rw [show wTil ⊥ V hV (conjSubgroup L (g : G)⁻¹) = wTil ⊥ V hV L from
      congrArg (fun B => commSub ⊤ B) hc]
    exact le_sup_left
  · rw [show wTil ⊥ V hV (conjSubgroup L (g : G)⁻¹)
        = wTil ⊥ V hV (conjSubgroup L x) from congrArg (fun B => commSub ⊤ B) hc]
    exact le_sup_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
