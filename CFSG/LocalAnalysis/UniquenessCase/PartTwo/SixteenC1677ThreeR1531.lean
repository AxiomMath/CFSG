module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeH1Om6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_row153_1
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case153_1 D V₀ V hV L) : Case167_1 D V₀ V hV L := by
  haveI : Finite (Vtil V₀ V hV) := inferInstance
  obtain ⟨hΩ, hnat, hsig, hrank, hs, -⟩ := h
  obtain ⟨ρ, θ, hρ, hequiv, hker⟩ := s168e3_star c hs
  rw [s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs] at hnat
  have hpull := s168e3_natOmegaMinus_pullback hnat ρ hρ θ hequiv
  rw [hker] at hpull
  obtain ⟨W', hinv, hcompl⟩ := s168e3_om6_ext_split (W := Vtil V₀ V hV)
    (s15_Infra_vtil_sq_eq_one V₀ V hV) hpull (fun a ha y hy => mem_fixV.1 hy a ha)
  have hcomm_le : commSub ⊤ (lBar V₀ V hV L) ≤ W' := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    obtain ⟨w', hw', y, hy, hwy⟩ :=
      Subgroup.mem_sup.mp (show w ∈ W' ⊔ fixV (lBar V₀ V hV L) from
        hcompl.sup_eq_top.symm ▸ Subgroup.mem_top w)
    have hfixy : x y = y := mem_fixV.1 hy x hx
    have hgen : x (w' * y) * (w' * y)⁻¹ = x w' * w'⁻¹ := by
      rw [map_mul, hfixy, mul_inv_rev]
      group
    rw [← hwy, hgen]
    exact W'.mul_mem (hinv x hx w' hw') (W'.inv_mem hw')
  have hw : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hWtop : W' = ⊤ := top_le_iff.mp (hw ▸ hcomm_le)
  have hfix : fixV (lBar V₀ V hV L) = ⊥ := by
    have hh := hcompl.inf_eq_bot
    rw [hWtop] at hh
    rwa [top_inf_eq] at hh
  rw [hfix] at hpull
  exact ⟨hΩ, hpull, hsig, hrank⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
