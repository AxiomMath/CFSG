module

public import CFSG.RankThree.PartOne.S10.Defs
import CFSG.RankThree.PartOne.S10.FiveCriticalResidual
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G]

theorem five_not_quasisimple_residual_of_centralizes [Finite G] {L D R : Subgroup G} {x : G}
    (hDL : D ≤ L) (hDn : (D.subgroupOf L).Normal) (hDsolv : Group.IsSolvable D)
    (hxD : D ≤ centralizer ({x} : Set G)) (hRP : R ≤ fiveResidual L x) (hRD : ⁅R, D⁆ ≠ ⊥) :
    ¬ CFSG.IsQuasisimple ↥(fiveResidual L x) := by
  intro hq
  set Y := L ⊓ centralizer ({x} : Set G) with hY
  have hDY : D ≤ Y := le_inf hDL hxD
  have hYL : Y ≤ L := inf_le_left
  have hPq : CFSG.IsQuasisimple ↥(perfectResidual ↥Y) :=
    isQuasisimple_of_map_subtype (L := Y) hq
  have hPsub : (perfectResidual ↥Y).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hDYn : (D.subgroupOf Y).Normal := ⟨fun d hd y => by
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    exact Subgroup.mem_subgroupOf.mp (hDn.conj_mem ⟨(d : G), hYL d.2⟩
      (Subgroup.mem_subgroupOf.mpr hd) ⟨(y : G), hYL y.2⟩)⟩
  have hDYsolv : Group.IsSolvable ↥(D.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hDY).toMonoidHom)
      (MulEquiv.injective _)
  have hcent := (LocalCores.component_solvable_centralizer hDYsolv
    (Subgroup.Normal.isSubnormal hDYn)).1 (perfectResidual ↥Y) ⟨hPq, hPsub⟩
  apply hRD
  have h : ⁅fiveResidual L x, D⁆ = ⊥ := by
    have h' := congrArg (Subgroup.map Y.subtype) hcent
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDY, Subgroup.map_bot] at h'
  exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono hRP le_rfl)

theorem mem_thetaQuotientCentralizer_of_le_centralizer {p : ℕ} {A L : Subgroup G} {c : G}
    (hcA : c ∈ A) (hL : L ≤ centralizer ({c} : Set G)) :
    c ∈ thetaQuotientCentralizer p A L := by
  have hcl : ∀ l ∈ L, c * l * c⁻¹ = l := fun l hl => by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hL hl)
    rw [← h]
    group
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨hcA, ?_, fun l hl => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      rw [hcl l hl]
      exact hl
    · intro hm
      have h1 : c * (c * l * c⁻¹) * c⁻¹ = c * l * c⁻¹ := hcl _ hm
      have h2 : c * (c * l * c⁻¹) = c * l := by
        calc c * (c * l * c⁻¹) = (c * (c * l * c⁻¹) * c⁻¹) * c := by group
          _ = (c * l * c⁻¹) * c := by rw [h1]
          _ = c * l := by group
      rw [mul_left_cancel h2] at hm
      exact hm
  · rw [hcl l hl, mul_inv_cancel]
    exact one_mem _

end CFSG.RankThree.PartOne.FiveCritical
