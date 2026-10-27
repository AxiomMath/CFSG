module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08d_simple_refl {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.coroot i ≠ 0 ∧ GGLinRefl (ggLin (p := 3) M.model (M.simple i)) ∧
      ∀ w, ggLin (p := 3) M.model (M.simple i) w - w ∈ Submodule.span (ZMod 3) {M.coroot i} := by
  have hα : M.root i (M.coroot i) = (2 : ZMod 3) := by
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  have hcoroot : M.coroot i ≠ 0 :=
    (ne_zero_of_apply_eq_two (p := 3) (by norm_num) hα).1
  have hs : ggLin (p := 3) M.model (M.simple i) = Module.reflection hα :=
    ggLin_eq_reflection M.model hα (M.simple_apply i)
  have hrefl : IsLinRefl (Module.reflection hα) := by
    refine ⟨M.coroot i, M.root i, hα, fun v => ?_⟩
    rw [Module.reflection_apply]
  refine ⟨hcoroot, ?_, ?_⟩
  ·
    rw [hs]
    exact (ggDepA_linRefl_iff (p := 3) (by norm_num) (Module.reflection hα)).mpr hrefl
  ·
    intro w
    rw [hs, Module.reflection_apply]
    have hmem : M.root i w • M.coroot i ∈ Submodule.span (ZMod 3) {M.coroot i} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    have hkey : (w - M.root i w • M.coroot i) - w = -(M.root i w • M.coroot i) := by abel
    rw [hkey]
    exact Submodule.neg_mem _ hmem

end CFSG.StandardType

end


