module

public import CFSG.Quasithin.H13.GoldschmidtC137L32ZCase
public import CFSG.Quasithin.Background.C134L32CorrM

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem zMod_case4W {L W G₀ S : Subgroup G} {u z : G} (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z)
    (h : CFSG.Quasithin.C134Case4Min G₀ S L) : ZModData L u z := by
  obtain ⟨⟨n, K, hK, hKin, α, -, hα, -, -, hU, -, -⟩, -⟩ := h
  exact ⟨⁅centerOf (c134Q G₀ L), L⁆, K, hK, hKin, α, 1, hα, Or.inl rfl, hU, D.hWU D.huW,
    cocycle_mem_commutator_of_perfect D.hLZ (centerOf_comm_gc _) D.hperf D.hcZ⟩

theorem zMod_of_caseW {L W G₀ S : Subgroup G} {u z : G} (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z)
    {i : ℕ} (hi : CFSG.Quasithin.IsC134CaseM i G₀ S L) (hi2 : 2 ≤ i) (hi4 : i ≤ 4) :
    ZModData L u z := by
  obtain rfl | rfl | rfl : i = 2 ∨ i = 3 ∨ i = 4 := by omega
  · exact zMod_case2 D hi
  · exact zMod_case3 D hi
  · exact zMod_case4W D hi

end CFSG.Quasithin.H13.U3.GC137
