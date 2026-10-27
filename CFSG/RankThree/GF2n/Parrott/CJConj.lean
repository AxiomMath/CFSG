module

public import CFSG.RankThree.GF2n.Parrott.CentralizerFusion
public import CFSG.RankThree.GF2n.Parrott.Setup

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable (D : QuotientData (z := z) hN)

theorem card_CJ_conj (g σ : ↥(H z)) :
    Nat.card (CJ z ((g : G) * (σ : G) * (g : G)⁻¹)) = Nat.card (CJ z (σ : G)) := by
  have h : CJ z ((g : G) * (σ : G) * (g : G)⁻¹) =
      (CJ z (σ : G)).map (MulAut.conj (g : G)) := by
    ext x
    rw [mem_CJ, Subgroup.mem_map]
    constructor
    · rintro ⟨hx, hxJ⟩
      refine ⟨(g : G)⁻¹ * x * (g : G), ?_, ?_⟩
      · rw [mem_CJ]
        refine ⟨?_, ?_⟩
        · rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
          calc ((g : G)⁻¹ * x * (g : G)) * (σ : G)
              = (g : G)⁻¹ * (x * ((g : G) * (σ : G) * (g : G)⁻¹)) * (g : G) := by group
            _ = (g : G)⁻¹ * (((g : G) * (σ : G) * (g : G)⁻¹) * x) * (g : G) := by rw [← hx]
            _ = (σ : G) * ((g : G)⁻¹ * x * (g : G)) := by group
        · have hxH : x ∈ H z := J_le_H hxJ
          have hmem := hN.conj_mem' (⟨x, hxH⟩ : ↥(H z))
            (by rwa [Subgroup.mem_subgroupOf]) (⟨(g : G), g.2⟩ : ↥(H z))
          simpa [Subgroup.mem_subgroupOf] using hmem
      · change (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x
        group
    · rintro ⟨y, hy, rfl⟩
      rw [mem_CJ] at hy
      refine ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        calc ((g : G) * y * (g : G)⁻¹) * ((g : G) * (σ : G) * (g : G)⁻¹)
            = (g : G) * (y * (σ : G)) * (g : G)⁻¹ := by group
          _ = (g : G) * ((σ : G) * y) * (g : G)⁻¹ := by rw [← hy.1]
          _ = ((g : G) * (σ : G) * (g : G)⁻¹) * ((g : G) * y * (g : G)⁻¹) := by group
      · have hyH : y ∈ H z := J_le_H hy.2
        have hmem := hN.conj_mem (⟨y, hyH⟩ : ↥(H z))
          (by simpa [Subgroup.mem_subgroupOf] using hy.2) (⟨(g : G), g.2⟩ : ↥(H z))
        simpa [Subgroup.mem_subgroupOf] using hmem
  rw [h, Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]

end CFSG.RankThree.GF2n.Parrott
