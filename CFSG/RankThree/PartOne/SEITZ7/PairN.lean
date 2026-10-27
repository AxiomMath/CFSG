module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open Subgroup CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
open scoped Pointwise

variable {G : Type*} [Group G]

theorem closure_cenGen_eq_top_of_plane [Finite G] {p e : ℕ} [Fact p.Prime] (S : Sylow p G)
    (E' : Subgroup G) (φ : ↥(S : Subgroup G) ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))))
    (hE'S : E' ≤ S) (hE'p : ∀ x ∈ E', x ^ p = 1) (hE'c : Nat.card E' = p ^ 2)
    (hmain : Subgroup.closure (cenGen E') = ⊤) (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) : Subgroup.closure (cenGen F) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hFpg : IsPGroup p ↥F := IsPGroup.of_card hFc
  obtain ⟨Q, hQ⟩ := hFpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S Q
  have hQS : (Q : Subgroup G) = cj (S : Subgroup G) c := by
    have h1 : ((c • S : Sylow p G) : Subgroup G) = (Q : Subgroup G) := by rw [hc]
    rw [← h1, Sylow.coe_subgroup_smul]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj F c⁻¹ ≤ S := by
    intro x hx
    have h1 : x ∈ cj (cj (S : Subgroup G) c) c⁻¹ := cj_le_cj (hQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  have hF' : cj F c⁻¹ = E' :=
    plane_unique hp φ hFS hE'S (fun x hx => pow_eq_one_of_mem_cj hFp hx) hE'p
      (by rw [card_cj]; exact hFc) hE'c
  have hF'' : F = cj E' c := by
    rw [← hF', cj_inv_cj]
  rw [hF'', closure_cenGen_cj, hmain]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective

end CFSG.RankThree.PartOne.SEITZ7
