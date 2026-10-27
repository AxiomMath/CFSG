module

public import Certificates.Data.CFSGNative.ExcCensus.Check
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusScan
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusAmb

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

variable {m : Fin 6} {T : Chk.Tabs}

theorem comb_not_mem_span {v y : V m} (hy : y ∉ Submodule.span (ZMod 3) {v}) {a b : ℕ}
    (hb : b = 1 ∨ b = 2) :
    (a : ZMod 3) • v + (b : ZMod 3) • y ∉ Submodule.span (ZMod 3) {v} := by
  intro h
  have hb0 : (b : ZMod 3) ≠ 0 := by rcases hb with rfl | rfl <;> decide
  have h2 : (b : ZMod 3) • y ∈ Submodule.span (ZMod 3) {v} :=
    (Submodule.add_mem_iff_right _
      (Submodule.smul_mem _ (a : ZMod 3) (Submodule.mem_span_singleton_self v))).mp h
  exact hy ((Submodule.smul_mem_iff _ hb0).mp h2)

theorem vec_combN_mem (cv cy a b : ℕ) :
    vec m (Chk.combN (dim m) cv cy a b) ∈ Submodule.span (ZMod 3) {vec m cv, vec m cy} :=
  Submodule.mem_span_pair.mpr ⟨_, _, (vec_combN m cv cy a b).symm⟩

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
