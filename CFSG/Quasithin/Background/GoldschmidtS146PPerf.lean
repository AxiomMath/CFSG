module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.Quasithin.GoldS146P

open Subgroup

@[expose] def PerfInLayer (X : Type*) [Group X] : Prop :=
  ∀ P : Subgroup X, ⁅P, P⁆ = P → P ≤ CFSG.layer X

theorem perfect_le_of_solvable_quotient {W : Type*} [Group W] (N : Subgroup W) [N.Normal]
    [Group.IsSolvable (W ⧸ N)] {P : Subgroup W} (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have h := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    ((QuotientGroup.mk' N).comp P.subtype)
  intro x hx
  have h1 := DFunLike.congr_fun h ⟨x, hx⟩
  exact (QuotientGroup.eq_one_iff x).mp h1

theorem perfInLayer_of_le_layer {W : Type*} [Group W] (N : Subgroup W) [N.Normal]
    [Group.IsSolvable (W ⧸ N)] (hN : N ≤ CFSG.layer W) : PerfInLayer W :=
  fun _ hP => (perfect_le_of_solvable_quotient N hP).trans hN

theorem le_layer_of_quasisimple_normal {W : Type*} [Group W] (N : Subgroup W) [hn : N.Normal]
    (hN : CFSG.IsQuasisimple ↥N) : N ≤ CFSG.layer W :=
  CFSG.LocalCores.component_le_layer ⟨hN, hn.isSubnormal⟩

theorem perfInLayer_of_quasisimple {W : Type*} [Group W] (N : Subgroup W) [N.Normal]
    [Group.IsSolvable (W ⧸ N)] (hN : CFSG.IsQuasisimple ↥N) : PerfInLayer W :=
  perfInLayer_of_le_layer N (le_layer_of_quasisimple_normal N hN)

theorem layer_map_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (CFSG.layer X).map e.toMonoidHom = CFSG.layer Y :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem PerfInLayer.of_equiv {X Y : Type*} [Group X] [Group Y] (e : Y ≃* X) (h : PerfInLayer X) :
    PerfInLayer Y := by
  intro P hP
  have hperf : ⁅P.map e.toMonoidHom, P.map e.toMonoidHom⁆ = P.map e.toMonoidHom := by
    rw [← Subgroup.map_commutator, hP]
  have h1 := h _ hperf
  rw [← layer_map_equiv e] at h1
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h1

end CFSG.Quasithin.GoldS146P
