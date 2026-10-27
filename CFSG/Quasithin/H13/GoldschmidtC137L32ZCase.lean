module

public import CFSG.Quasithin.H13.GoldschmidtC137L32ZGen
public import CFSG.Quasithin.Background.C41PfCorr
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZPerf

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] def ZModData (L : Subgroup G) (u z : G) : Prop :=
  ∃ (M : Subgroup G) (K : Type) (_ : Field K) (_ : Fintype K) (α : ↥L →* ↥(StatedSL 3 K))
    (j : ℕ), IsModO2Surj L α ∧ (j = 1 ∨ j = 2) ∧ IsSumOfNaturalModulesVia L M ⊥ α false j ∧
      u ∈ M ∧ ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ M

theorem zMod_case2 {L W G₀ S : Subgroup G} {u z : G} (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z)
    (h : IsC134Case2 G₀ S L) : ZModData L u z := by
  obtain ⟨⟨n, K, hK, hKin, α, -, hα, hM⟩, -⟩ := h
  exact ⟨c134Q G₀ L, K, hK, hKin, α, 2, hα, Or.inr rfl, hM, D.hWQ D.huW, D.hcQ⟩

theorem zMod_case3 {L W G₀ S : Subgroup G} {u z : G} (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z)
    (h : IsC134Case3 G₀ S L) : ZModData L u z := by
  obtain ⟨⟨n, K, hK, hKin, α, -, hα, hM, -⟩, -⟩ := h
  exact ⟨centerOf (c134Q G₀ L), K, hK, hKin, α, 1, hα, Or.inl rfl, hM, D.hWZ D.huW, D.hcZ⟩

theorem zMod_case4 {L W G₀ S : Subgroup G} {u z : G} (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z)
    (h : C134CorrLocal.IsC134Case4Corr G₀ S L) : ZModData L u z := by
  obtain ⟨⟨n, K, hK, hKin, α, -, hα, -, -, -, hU, -, -, -⟩, -⟩ := h
  exact ⟨⁅centerOf (c134Q G₀ L), L⁆, K, hK, hKin, α, 1, hα, Or.inl rfl, hU, D.hWU D.huW,
    cocycle_mem_commutator_of_perfect D.hLZ (centerOf_comm_gc _) D.hperf D.hcZ⟩

theorem zMod_of_case {L W G₀ S : Subgroup G} {u z : G} (D : ZFacts L (CFSG.Open.pCoreOf 2 G₀) W u z)
    {i : ℕ} (hi : C134CorrLocal.IsC134CaseCorr i G₀ S L) (hi2 : 2 ≤ i) (hi4 : i ≤ 4) :
    ZModData L u z := by
  obtain rfl | rfl | rfl : i = 2 ∨ i = 3 ∨ i = 4 := by omega
  · exact zMod_case2 D hi
  · exact zMod_case3 D hi
  · exact zMod_case4 D hi

end CFSG.Quasithin.H13.U3.GC137
