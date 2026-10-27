module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16f_mul_self_eq_one_of_mem_cent (hW : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {R : Subgroup W} (hKtriv : commSub ⊤ K ≤ R)
    {g : MulAut W} (hgK : g ∈ K) (hgC : g ∈ centSub R) : g * g = 1 := by
  ext w
  simp only [MulAut.mul_apply, MulAut.one_apply]
  let r : W := g w * w⁻¹
  have hmem : r ∈ R :=
    hKtriv (Subgroup.subset_closure ⟨g, hgK, w, Subgroup.mem_top w, rfl⟩)
  have hfix : g r = r := (mem_centSub.mp hgC) r hmem
  have hrw : g w = r * w := by
    show g w = (g w * w⁻¹) * w
    rw [mul_assoc, inv_mul_cancel, mul_one]
  calc
    g (g w) = g (r * w) := by rw [hrw]
    _ = g r * g w := map_mul g r w
    _ = r * g w := by rw [hfix]
    _ = r * (r * w) := by rw [hrw]
    _ = r ^ 2 * w := by rw [← mul_assoc, sq]
    _ = 1 * w := by rw [hW r]
    _ = w := one_mul w

theorem swap_faithful_on_commSub (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hY : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hK : IsComponentOf K Y) {R : Subgroup W} (hKR : StableUnder K R)
    (hKtriv : commSub ⊤ K ≤ R) : K ⊓ centSub R = ⊥ := by
  classical
  have hNnorm : ((K ⊓ centSub R).subgroupOf K).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr ?_
    intro n k hn hk
    have hnK : n ∈ K := (Subgroup.mem_inf.mp hn).1
    have hnC : n ∈ centSub R := (Subgroup.mem_inf.mp hn).2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem hk hnK) (K.inv_mem hk)
    · rw [mem_centSub]
      intro r hr
      rw [MulAut.mul_apply, MulAut.mul_apply]
      rw [mem_centSub.mp hnC (k⁻¹ r) (hKR k⁻¹ (K.inv_mem hk) r hr)]
      exact MulAut.apply_inv_self W k r
  have hNsubK : CFSG.Open.IsSubnormal (K ⊓ centSub R) K :=
    CFSG.Open.IsSubnormal.step inf_le_left hNnorm (CFSG.Open.IsSubnormal.refl K)
  have hNsubY : CFSG.Open.IsSubnormal (K ⊓ centSub R) Y := hNsubK.trans hK.2.1
  have hN2 : IsPGroup 2 ↥(K ⊓ centSub R) := by
    intro n
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by
      simpa [sq] using
        w16f_mul_self_eq_one_of_mem_cent hW hKtriv (Subgroup.mem_inf.mp n.2).1
          (Subgroup.mem_inf.mp n.2).2)
  have hNleP : K ⊓ centSub R ≤ pCoreOf 2 Y :=
    CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hNsubY hN2
  have hPle : pCoreOf 2 Y ≤ Y :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 Y
  have hPnorm : ((pCoreOf 2 Y).subgroupOf Y).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 Y Y le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hP2 : IsPGroup 2 (pCoreOf 2 Y) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 Y
  have hPbot : pCoreOf 2 Y = ⊥ := hY (pCoreOf 2 Y) hPle hPnorm hP2
  exact bot_unique (hPbot ▸ hNleP)

end CFSG.LocalAnalysis.WeakClosure81
