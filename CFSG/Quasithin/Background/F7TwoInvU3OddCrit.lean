module

public import CFSG.Quasithin.Background.F7TwoInvU3OddGen
public import CFSG.Quasithin.Background.F7TwoInvAutWrap

public section

namespace CFSG.Quasithin.F7Two.U3Odd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.RankThree.CentralLiftU

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem invAutGen_hyp_of_diag (hp2 : p ≠ 2) (hs : IsSimpleGroup (hypPSU h 1 1))
    {α : MulAut (hypPSU h 1 1)} (hα2 : α * α = 1) (hα1 : α ≠ 1) {D : GL (HypIndex 1 1) K}
    (hD : ∃ d, (D : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d) (σ : K ≃+* K)
    (hαD : ∀ g : hypSU h 1 1, ∃ hg : D * glAut σ (g : GL (HypIndex 1 1) K) * D⁻¹ ∈ hypSU h 1 1,
      α (hypProj h 1 1 g) = hypProj h 1 1 ⟨_, hg⟩) :
    InvAutGen (hypPSU h 1 1) α := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  refine invAutGen_of_odd_sup hs (hypPSU_nonabelian hs) hα2 hα1
    (U₁ := (hypUnitriangular h 1 1).map (hypProj h 1 1))
    (U₂ := (lowerU h).map (hypProj h 1 1)) ?_ ?_ ?_ ?_ (sup_lowerU_map_eq_top hs)
  · exact (odd_natCard_of_isPGroup hp2 (isPGroup_hypUnitriangular (h := h) le_rfl)).of_dvd_nat
      (Subgroup.card_map_dvd _ _)
  · exact (odd_natCard_of_isPGroup hp2 (isPGroup_lowerU hp2)).of_dvd_nat
      (Subgroup.card_map_dvd _ _)
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hg, hα⟩ := hαD u
    rw [hα]
    exact ⟨⟨_, hg⟩, mem_hypUnitriangular_iff.mpr
      (conj_mem_fullUnitriangular_of_diag hD σ (mem_hypUnitriangular_iff.mp hu)), rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hg, hα⟩ := hαD u
    rw [hα]
    exact ⟨⟨_, hg⟩, mem_lowerU.mpr (conj_mem_lowerU_aux hD σ (mem_lowerU.mp hu)), rfl⟩

end CFSG.Quasithin.F7Two.U3Odd
