module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.GoldschmidtS146PPerf

public section

namespace CFSG.Quasithin.GoldS146P

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem center_eq_bot_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) : Subgroup.center L = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center L := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem conj_injective_of_simple {L : Type*} [Group L] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) : Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut L => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  rw [center_eq_bot_of_simple hnc, Subgroup.mem_bot] at hmem
  exact hmem

theorem perfInLayer_mulAut (L : Type*) [Group L] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a) [Group.IsSolvable (Outer L)] : PerfInLayer (MulAut L) := by
  have hq : CFSG.IsQuasisimple L := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have e : L ≃* ↥(inner L) := MonoidHom.ofInjective (conj_injective_of_simple hnc)
  exact perfInLayer_of_quasisimple (inner L) (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

end CFSG.Quasithin.GoldS146P
