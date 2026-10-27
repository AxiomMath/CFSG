module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiNe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ACaseFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s15_inf_fixV_wTil_eq_bot_of_ne_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV₀ : V₀ ≠ ⊥) :
    wTil V₀ V h.isElemAbelian L ⊓ fixV (barSub V₀ V h.isElemAbelian L) = ⊥ := by
  set hV := h.isElemAbelian
  set X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G)) with hXdef
  have hXle : X ≤ Mbar D.M V₀ V hV := s15_Infra_iSup_barSub_le h
  have hXn := s15_Infra_iSup_barSub_normal h
  have hstab : ∀ φ ∈ Mbar D.M V₀ V hV, ∀ u ∈ fixV X, φ u ∈ fixV X := by
    intro φ hφ u hu
    rw [mem_fixV] at hu ⊢
    intro x hx
    have hx' : φ⁻¹ * x * φ ∈ X := by
      have hmem : (⟨x, hXle hx⟩ : Mbar D.M V₀ V hV) ∈ X.subgroupOf (Mbar D.M V₀ V hV) := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have := hXn.conj_mem _ hmem (⟨φ, hφ⟩ : Mbar D.M V₀ V hV)⁻¹
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
    have hfix := hu _ hx'
    calc x (φ u) = φ ((φ⁻¹ * x * φ) u) := by
          simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = φ u := by rw [hfix]
  rcases s15_Kbar_irreducible h.hyp125 hV₀ (fixV X) hstab with hC | hC
  · refine le_bot_iff.1 fun z hz => ?_
    have hzX : z ∈ fixV X := by
      rw [mem_fixV]
      intro x hx
      have hle : X ≤ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) z := by
        refine iSup_le fun m => ?_
        intro y hy
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        by_cases hm : (m : G) ∈ nBar D.M V₀ V hV L
        · rw [(s15_Infra_mem_nBar_iff h.hyp125 hV m.2).1 hm] at hy
          exact (mem_fixV.mp hz.2) y hy
        · exact (mem_fixV.mp ((c23a_cross_fix h m.2 hm).1 hz.1)) y hy
      have := hle hx
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    rw [hC] at hzX
    exact hzX
  · have hLX : barSub V₀ V hV L ≤ X := s15_semi_le_iSup_barSub h
    have hW : wTil V₀ V hV L = ⊥ := by
      unfold wTil
      rw [commSub_eq_bot_iff]
      intro v _ x hx
      have hv : v ∈ fixV X := by rw [hC]; exact Subgroup.mem_top v
      exact (mem_fixV.mp hv) x (hLX hx)
    rw [hW, bot_inf_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
