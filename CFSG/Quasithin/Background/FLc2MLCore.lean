module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G]

theorem eq_of_map_top {L SL K : Subgroup G} {n : ℕ} (hKL : K ≤ L) (hSLK : SL ≤ K)
    (α : ↥L →* SLt n) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ SL)
    (h : (K.subgroupOf L).map α = ⊤) : K = L := by
  refine le_antisymm hKL fun y hy => ?_
  have : α ⟨y, hy⟩ ∈ (K.subgroupOf L).map α := by rw [h]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hky⟩ := this
  have hk1 : α (k⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, hky, inv_mul_cancel]
  have hs : ((k⁻¹ * ⟨y, hy⟩ : ↥L) : G) ∈ SL := hker _ hk1
  have hyk : y = (k : G) * ((k⁻¹ * ⟨y, hy⟩ : ↥L) : G) := by simp
  rw [hyk]
  exact K.mul_mem hk (hSLK hs)

theorem eq_of_reflections [Finite G] {L SL P Ml : Subgroup G} {n c : ℕ} (hc : IsNode n c)
    (hSLP : SL ≤ P) (hPL : P ≤ L) (hPMl : P ≤ Ml) (hMlL : Ml ≤ L)
    (α : ↥L →* SLt n) (hker : ∀ x : ↥L, α x = 1 → (x : G) ∈ SL)
    (hB : (SL.subgroupOf L).map α = Ut n) (hPne : P ≠ L) (hMlne : Ml ≠ L)
    (hR : ∀ i, ∀ hi : IsNode n i, i ≠ c →
      ∃ x : ↥L, α x = reflection n (ZMod 2) i hi.1 hi.2 ∧ (x : G) ∈ P) : Ml = P := by
  have hmap : ∀ K : Subgroup G, SL ≤ K → K ≤ L → K ≠ L → (∀ i, ∀ hi : IsNode n i, i ≠ c →
      ∃ x : ↥L, α x = reflection n (ZMod 2) i hi.1 hi.2 ∧ (x : G) ∈ K) →
      cuts ((K.subgroupOf L).map α) = {c} := by
    intro K hSLK hKL hKne hRK
    set J : Subgroup (SLt n) := (K.subgroupOf L).map α with hJ
    have hUJ : Ut n ≤ J := by
      rw [← hB]
      exact Subgroup.map_mono fun s hs => hSLK hs
    have hJe : J = QI n (cuts J) := eq_QI_cuts hUJ
    have hsub : cuts J ⊆ {c} := by
      intro i hi
      have hin := isNode_of_mem_cuts hi
      by_contra hic
      obtain ⟨x, hx, hxK⟩ := hRK i hin hic
      have hrJ : reflection n (ZMod 2) i hin.1 hin.2 ∈ J := ⟨x, hxK, hx⟩
      rw [hJe] at hrJ
      exact (reflection_mem_QI hin).1 hrJ hi
    have hne : (cuts J).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hKne
      refine eq_of_map_top hKL hSLK α hker ?_
      rw [← hJ, hJe, hempty]
      simp
    obtain ⟨j, hj⟩ := hne
    have hjc : j = c := hsub hj
    subst hjc
    exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 hj)
  have hP := hmap P hSLP hPL hPne hR
  have hM := hmap Ml (hSLP.trans hPMl) hMlL hMlne (fun i hi hic => by
    obtain ⟨x, hx, hxP⟩ := hR i hi hic
    exact ⟨x, hx, hPMl hxP⟩)
  have hUP : Ut n ≤ (P.subgroupOf L).map α := by
    rw [← hB]
    exact Subgroup.map_mono fun s hs => hSLP hs
  have hUM : Ut n ≤ (Ml.subgroupOf L).map α := by
    rw [← hB]
    exact Subgroup.map_mono fun s hs => (hSLP.trans hPMl) hs
  have heq : (Ml.subgroupOf L).map α = (P.subgroupOf L).map α :=
    eq_of_cuts_eq hUM hUP (by rw [hM, hP])
  refine le_antisymm (fun y hy => ?_) hPMl
  have hyL : y ∈ L := hMlL hy
  have : α ⟨y, hyL⟩ ∈ (P.subgroupOf L).map α := by
    rw [← heq]
    exact ⟨⟨y, hyL⟩, hy, rfl⟩
  obtain ⟨p, hp, hpy⟩ := this
  have hk1 : α (p⁻¹ * ⟨y, hyL⟩) = 1 := by rw [map_mul, map_inv, hpy, inv_mul_cancel]
  have hs : ((p⁻¹ * ⟨y, hyL⟩ : ↥L) : G) ∈ SL := hker _ hk1
  have hyp : y = (p : G) * ((p⁻¹ * ⟨y, hyL⟩ : ↥L) : G) := by simp
  rw [hyp]
  exact P.mul_mem hp (hSLP hs)

end CFSG.Quasithin.FLc
