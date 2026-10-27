module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 Theorem82At)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem asc83CComponent_of_mem_calC {M L : Subgroup G} (h : L ∈ calC M) :
    CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent M L :=
  ⟨h.1.le, h.1, h.2.1, inferInstance, h.2.2⟩

theorem hyp81_of_f08 {M L : Subgroup G} (h : F08.Hyp81 M L) :
    CFSG.Yardstones.Mf4cdcdf2e013.Hyp81 M L := by
  obtain ⟨hsub, hperf, h3, hcases⟩ := h
  refine ⟨hsub.le, hsub, hperf, h3, ?_⟩
  rcases hcases with hq | ⟨L₁, L₂, L₃, h₁, h₂, h₃, r₁, r₂, r₃, l₁, l₂, l₃, hprod⟩
  · obtain ⟨hp, hs, -⟩ := hq
    exact Or.inl ⟨inferInstance, hp.commutator_eq_top, hs⟩
  · refine Or.inr ⟨L₁, L₂, L₃, ?_, l₁, l₂, l₃, asc83CComponent_of_mem_calC h₁, r₁,
      asc83CComponent_of_mem_calC h₂, r₂, asc83CComponent_of_mem_calC h₃, r₃, ?_⟩
    · apply le_antisymm
      · intro x hx
        have hx' : x ∈ (L₁ : Set G) * L₂ * L₃ := by rw [← hprod]; exact hx
        obtain ⟨y, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx'
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right hc)
      · exact sup_le (sup_le l₁ l₂) l₃
    · intro x hx
      have hx' : x ∈ (L₁ : Set G) * L₂ * L₃ := by rw [← hprod]; exact hx
      obtain ⟨y, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx'
      exact ⟨a, ha, b, hb, c, hc, rfl⟩

theorem r82_of_theorem82At {D : Data G} (h : Theorem82At D.M) : F08.R82 D :=
  fun L hL => h L (hyp81_of_f08 hL)

theorem r82_dataOfSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (h : Theorem82At S.M) : F08.R82 (UC6.dataOfSetup4 hS hU S) :=
  r82_of_theorem82At h

end CFSG.LocalAnalysis.UniquenessCase.UC22
