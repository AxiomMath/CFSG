module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup CFSG.HallHigman
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_opp_self {p : ℕ} {Y : Subgroup G} {w : G} (hw : w ∈ Y) {x : G}
    (hx : x ∈ Opp p Y) : w * x * w⁻¹ ∈ Opp p Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨Y.mul_mem (Y.mul_mem hw hx.1) (Y.inv_mem hw), ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    exact ⟨k, by rw [← hk]; exact MulEquiv.orderOf_eq (MulAut.conj w) x⟩
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [show w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

omit [Finite G] in
theorem le_normalizer_opp_self (p : ℕ) (Y : Subgroup G) :
    Y ≤ normalizer (Opp p Y : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_opp_self hw hx, fun hx => ?_⟩
  simpa [mul_assoc] using conj_mem_opp_self (Y.inv_mem hw) hx

omit [Finite G] in
theorem normal_opp_subgroupOf (p : ℕ) (Y : Subgroup G) : ((Opp p Y).subgroupOf Y).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((Subgroup.closure_le Y).mpr fun _ hx => hx.1)).mpr (le_normalizer_opp_self p Y)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
