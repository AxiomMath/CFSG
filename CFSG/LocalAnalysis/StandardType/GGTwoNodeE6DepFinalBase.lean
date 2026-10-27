
module

public import CFSG.LocalAnalysis.StandardType.GGReflMovingSound
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepChart
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepExclusion
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6AllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumer

@[expose] public section

namespace CFSG.StandardType

open CFSG.DepFrame CFSG.NineAll CFSG.TwoNodeSmall CFSG.ReflExt

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6DepH_not_span_aux :
    ∀ (j k : Fin 6), j ≠ k → ∀ a : ZMod 3,
      a • (e6DepPt ()).vec (e6DepH k) ≠ (e6DepPt ()).vec (e6DepH j) := by
  decide +kernel

private theorem e6DepH_not_span (j k : Fin 6) (hjk : j ≠ k) :
    (e6DepPt ()).vec (e6DepH j) ∉
      Submodule.span (ZMod 3) {(e6DepPt ()).vec (e6DepH k)} := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  exact e6DepH_not_span_aux j k hjk a ha

private theorem e6DepH_nbr_aux :
    ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ ((CartanMatrix.E 6 j i : ℤ) : ZMod 3) ≠ 0 := by
  decide +kernel

theorem lr6E6DepAll_of_frame (hfrm : ∃ T, verifyAllM (e6DepPt ()) T = true) : LR6E6DepAll := by
  intro p _ hp V _ _ _ hV h α x r hfr hr A hrA hnt hcard s hsA hsx c β hs hβc
  subst hp
  obtain ⟨ε, hεh, hεα, hεx⟩ := e6Dep_chart hV h α x hfr
  obtain ⟨T, hT⟩ := hfrm
  haveI : Fact (e6DepPt ()).p.Prime := ⟨Nat.prime_three⟩
  have hcard' : Nat.card ↥A ≤ (e6DepPt ()).bound := by
    rw [show (e6DepPt ()).bound = 3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) by
      decide +kernel]
    exact hcard
  have hh : ∀ j k : Fin 6, j ≠ k → h j ∉ Submodule.span (ZMod 3) {h k} := by
    intro j k hjk hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    apply e6DepH_not_span j k hjk
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    calc
      a • (e6DepPt ()).vec (e6DepH k) = a • ε (h k) := by rw [hεh k]
      _ = ε (a • h k) := (map_smul ε a (h k)).symm
      _ = ε (h j) := by rw [ha]
      _ = (e6DepPt ()).vec (e6DepH j) := hεh j
  have hdiag : ∀ i : Fin 6, α i (h i) = 2 := by
    intro i
    rw [hfr.pair i i]
    simp
  have hnbr : ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ α j (h i) ≠ 0 := by
    intro i
    obtain ⟨j, hji, hj⟩ := e6DepH_nbr_aux i
    refine ⟨j, hji, ?_⟩
    rw [hfr.pair j i]
    exact hj
  have hsr : GGLinRefl s :=
    (ggDepA_linRefl_iff (p := 3) (by decide) s).mpr ⟨c, β, hβc, hs⟩
  have hcomm : ∀ i, s * r i = r i * s :=
    movingFrame_core (e6DepPt ()) (by decide) hT (fun k => ⟨e6DepF k, e6DepH k⟩) rfl ε h α x r hr
      A hrA hεh hεα hεx hnt hcard' s hsA hsr hsx
  exact ggDep_mem_span_of_commute (p := 3) (by decide) hfr.fix hdiag hnbr hh r hr hs hβc hcomm

end CFSG.StandardType

end
