module

public import CFSG.Quasithin.Vol2.Ch11SecA13Basic
public import CFSG.Quasithin.Vol2.Ch11SecA14Delta2
public import CFSG.Quasithin.Vol2.Ch11SecAFactsLine

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem autOn_fix_centralizer (L V : Subgroup G) :
    ∀ g ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, g z = z := by
  intro g hg z hz
  obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
  apply Subtype.ext
  rw [conjV_apply_coe]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hz
  rw [hz x hx, mul_inv_cancel_right]

theorem lineFacts (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {U₂ : Subgroup G} (hU₂ : IsVi T L I n 2 U₂) :
    LineFacts (autOn L (fsuV T I)) ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
      (U₂.subgroupOf (fsuV T I)) := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hZ := autOn_fix_centralizer L (fsuV T I)
  have f₂ := isFlagW_of_isVi h hU₂
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
  rcases hc with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
  · exact hL3 K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ f₂
  · exact (hLp K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ f₂).1
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    exact (hLg K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ f₂).1

theorem perfCentFacts (hLp : FactLineSp4) (hLg : FactLineG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n) {U₂ : Subgroup G}
    (hU₂ : IsVi T L I n 2 U₂) :
    PerfCentFacts (autOn L (fsuV T I)) ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
      (U₂.subgroupOf (fsuV T I)) := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hZ := autOn_fix_centralizer L (fsuV T I)
  have f₂ := isFlagW_of_isVi h hU₂
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
  rcases hc with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
  · exact (hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact (hLp K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ f₂).2
      (commV_autOn_eq_top h)
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    exact (hLg K n h.one_lt hK _ hsq _ _ π hπ hZ _ (isSylowTwoOf_P h) _ f₂).2
      (commV_autOn_eq_top h)

theorem perfectCore_eq_autOn_lOf (h : Hyp11 G T L I n) {U : Subgroup G} (hU : U ≤ fsuV T I) :
    perfectCore (autOn L (fsuV T I) ⊓ stabW (U.subgroupOf (fsuV T I))) =
      autOn (LOf L U) (fsuV T I) :=
  (autOn_lOf (L_le_normalizer_fsuV h) hU).symm

theorem pCoreOf_perfectCore_eq (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {U : Subgroup G}
    (hU : U ≤ fsuV T I) :
    pCoreOf 2 (perfectCore (autOn L (fsuV T I) ⊓ stabW (U.subgroupOf (fsuV T I)))) =
      autOn (pCoreOf 2 (LOf L U)) (fsuV T I) := by
  rw [perfectCore_eq_autOn_lOf h hU,
    autOn_pCoreOf ((lOf_le L U).trans (L_le_normalizer_fsuV h)) (isPGroup_lOf_inf h1102 h U)]

end CFSG.Quasithin.Vol2.Ch11.SecA
