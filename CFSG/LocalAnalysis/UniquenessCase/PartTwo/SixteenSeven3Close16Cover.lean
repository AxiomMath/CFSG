module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem close16_isAlt_quot (hS : Close16Setting D V L hV) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hbarY : barSub ⊥ V hV Y = lBar ⊥ V hV L)
    [((Y ⊓ F11.CTilde D.M ⊥ V).subgroupOf Y).Normal] :
    IsAlt (↥Y ⧸ (Y ⊓ F11.CTilde D.M ⊥ V).subgroupOf Y) 8 := by
  obtain ⟨φ, hφ, hker⟩ := close16_exists_hom_barSub (hV := hV) (close16_le_stabTil hS) hYM
  obtain ⟨e⟩ := close16_lbar_isAlt hS
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans
      ((MulEquiv.subgroupCongr hbarY).trans e))⟩

theorem close16_exists_Y (h127 : R127 D) (h119 : F11.R119 D) (hS : Close16Setting D V L hV) :
    ∃ Y : Subgroup G, Close16Pack D V L hV Y := by
  obtain ⟨X, Y, hCX, hXM, hXN, hbarX, hYX, hYperf, hO2E, hXY, hYC, hbarY⟩ :=
    close16_apply_r119 h127 h119 hS
  have hMs : D.M ≤ stabTil ⊥ V := close16_le_stabTil hS
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer ⊥ V)
  have hYM : Y ≤ D.M := hYX.trans hXM
  obtain ⟨φY, -, hkerY⟩ := close16_exists_hom_barSub (hV := hV) hMs hYM
  haveI hnormY : ((Y ⊓ F11.CTilde D.M ⊥ V).subgroupOf Y).Normal := hkerY ▸ φY.normal_ker
  have hker : Y ⊓ F11.CTilde D.M ⊥ V = pCoreOf 2 Y :=
    close16_ker_eq_pcore hYperf hO2E hYC (close16_isAlt_quot hS hYM hbarY)
  have hY2 : IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M ⊥ V) := by
    rw [hker]
    exact CFSG.pCore_isPGroup.map _
  have hXYC : X = Y ⊔ F11.CTilde D.M ⊥ V := by
    refine le_antisymm (fun x hx => ?_) (sup_le hYX hCX)
    have hxs : x ∈ stabTil ⊥ V := hMs (hXM hx)
    have hxbar := actTil_mem_barSub ⊥ V hV hx hxs
    rw [hbarX, ← hbarY] at hxbar
    obtain ⟨g, hgY, hg⟩ := (mem_barSub ⊥ V hV Y _).1 hxbar
    have hxc : x * (g : G)⁻¹ ∈ F11.CTilde D.M ⊥ V := by
      rw [mem_cTilde_iff hV hMn]
      refine ⟨D.M.mul_mem (hXM hx) (D.M.inv_mem (hYM hgY)),
        (stabTil ⊥ V).mul_mem hxs ((stabTil ⊥ V).inv_mem g.2), ?_⟩
      have h1 : (⟨x * (g : G)⁻¹, (stabTil ⊥ V).mul_mem hxs ((stabTil ⊥ V).inv_mem g.2)⟩ :
          ↥(stabTil ⊥ V)) = ⟨x, hxs⟩ * g⁻¹ := rfl
      rw [h1, map_mul, map_inv, hg, mul_inv_cancel]
    have hmem := Subgroup.mul_mem_sup hxc hgY
    rw [inv_mul_cancel_right, sup_comm] at hmem
    exact hmem
  obtain ⟨φX, hφX, hkerX⟩ := close16_exists_hom_barSub (hV := hV) hMs hXM
  haveI hsimple : IsSimpleGroup ↥(barSub ⊥ V hV X) := by
    rw [hbarX]; exact close16_lbar_simple hS
  have hnc : ¬ IsMulCommutative ↥(barSub ⊥ V hV X) := by
    rw [hbarX]; exact close16_lbar_not_commutative hS
  obtain ⟨hXC, hXab⟩ := close16_simple_of_hom hCX hnc φX hφX
    (by rw [hkerX, inf_eq_right.2 hCX])
  exact ⟨Y, hYM, close16_normal_of_cover (s15_Three_cTilde_normal hV hMs) hXM hXN hCX hYX hXY
    hYperf hXYC hY2 hXC hXab, hYperf, hbarY, hker⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
