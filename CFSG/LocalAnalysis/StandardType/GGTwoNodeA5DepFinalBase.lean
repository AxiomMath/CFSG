
module

public import CFSG.LocalAnalysis.StandardType.GGReflDepSound
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepChart
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepExclusion
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumer

@[expose] public section

namespace CFSG.StandardType

open CFSG.DepFrame CFSG.NineAll CFSG.TwoNodeSmall CFSG.ReflExt

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem a5DepH_not_span_aux :
    ∀ (j k : Fin 5), j ≠ k → ∀ a : ZMod 3,
      a • (a5DepPt ()).vec (a5DepH k) ≠ (a5DepPt ()).vec (a5DepH j) := by
  decide +kernel

private theorem a5DepH_not_span (j k : Fin 5) (hjk : j ≠ k) :
    (a5DepPt ()).vec (a5DepH j) ∉
      Submodule.span (ZMod 3) {(a5DepPt ()).vec (a5DepH k)} := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  exact a5DepH_not_span_aux j k hjk a ha

theorem lr6A5DepAll_of_frame
    (hfrm : ∃ T, verifyAllD (a5DepPt ()) a5DepBstab T = true) : LR6A5DepAll := by
  intro p _ hp V _ _ _ hV h α x r hfr hr A hrA hrg hnt hcard hstab
  subst hp
  obtain ⟨ε, hεh, hεα, hεx⟩ := a5Dep_chart hV h α x hfr
  obtain ⟨T, hT⟩ := hfrm
  haveI : Fact (a5DepPt ()).p.Prime := ⟨Nat.prime_three⟩
  have hcard' : Nat.card ↥A ≤ (a5DepPt ()).bound := by
    rw [show (a5DepPt ()).bound = 3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) by
      decide +kernel]
    exact hcard
  have hstab' : Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) x) ≤ a5DepBstab := by
    rw [show a5DepBstab = (3 - 1) * 6 * Nat.factorial 6 by decide +kernel]
    exact hstab
  have hh : ∀ j k : Fin (6 - 1), j ≠ k → h j ∉ Submodule.span (ZMod 3) {h k} := by
    intro j k hjk hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    apply a5DepH_not_span j k hjk
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    calc
      a • (a5DepPt ()).vec (a5DepH k) = a • ε (h k) := by rw [hεh k]
      _ = ε (a • h k) := (map_smul ε a (h k)).symm
      _ = ε (h j) := by rw [ha]
      _ = (a5DepPt ()).vec (a5DepH j) := hεh j
  rcases depFrame_core (a5DepPt ()) (by decide : (a5DepPt ()).p ≠ 2) hT
      (fun k => ⟨a5DepF k, a5DepH k⟩) rfl ε h α x r hr A hrA hεh hεα hεx hrg hnt
      hcard' hstab' with hw | hcomm
  · exact Or.inl hw
  · right
    intro s hsA hsx c β hs hβc
    have hsr : GGLinRefl s :=
      (ggDepA_linRefl_iff (p := 3) (by decide) s).mpr ⟨c, β, hβc, hs⟩
    exact ggDepA_mem_span_of_commute (p := 3) (by decide) (by norm_num : 3 ≤ 6)
      hfr hh r hr hs hβc (hcomm s hsA hsr hsx)

end CFSG.StandardType

end
