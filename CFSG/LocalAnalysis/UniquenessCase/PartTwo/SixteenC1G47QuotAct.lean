module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c1_G47_quot_action {Γ : Type} [Group Γ] {H E Z : Subgroup Γ}
    (hHE : H ≤ normalizer (E : Set Γ)) (hZE : Z ≤ E)
    (hZc : ∀ h ∈ H, ∀ z ∈ Z, h * z = z * h) [(Z.subgroupOf E).Normal]
    (hQ : ∀ q : ↥H, q ∈ CFSG.pCore 2 ↥H → ∀ e ∈ E, (q : Γ) * e * (q : Γ)⁻¹ * e⁻¹ ∈ Z) :
    ∃ ρ : (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut (↥E ⧸ Z.subgroupOf E),
      ∀ (h : ↥H) (e e' : ↥E), (e' : Γ) = (h : Γ) * (e : Γ) * (h : Γ)⁻¹ →
        ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) (QuotientGroup.mk e) = QuotientGroup.mk e' := by
  classical
  haveI : Subgroup.Normalizes H E := ⟨hHE⟩
  let K : Subgroup ↥E := Z.subgroupOf E
  haveI hKnormal : K.Normal := by
    change (Z.subgroupOf E).Normal
    infer_instance
  let ρH : ↥H →* MulAut ↥E := MulDistribMulAction.toMulAut ↥H ↥E
  have hρH : ∀ (h : ↥H) (e : ↥E), ((ρH h e : ↥E) : Γ) = (h : Γ) * (e : Γ) * (h : Γ)⁻¹ :=
    fun _ _ => rfl
  have hfix : ∀ (h : ↥H) (k : ↥E), (k : Γ) ∈ Z → ρH h k = k := by
    intro h k hk
    apply Subtype.ext
    rw [hρH, hZc h h.2 (k : Γ) hk]
    group
  have hmap : ∀ h : ↥H, K.map (ρH h : ↥E →* ↥E) = K := by
    intro h
    apply le_antisymm
    · intro k hk
      rw [Subgroup.mem_map] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      have hfix' : (ρH h : ↥E →* ↥E) k' = k' :=
        hfix h k' (Subgroup.mem_subgroupOf.mp hk')
      rw [hfix']
      exact hk'
    · intro k hk
      exact ⟨k, hk, hfix h k (Subgroup.mem_subgroupOf.1 hk)⟩
  let ρ₁ : ↥H →* MulAut (↥E ⧸ K) :=
    { toFun := fun h => QuotientGroup.congr K K (ρH h) (hmap h)
      map_one' := by
        apply MulEquiv.ext
        intro x
        induction x using QuotientGroup.induction_on
        simp only [QuotientGroup.congr_mk, map_one, MulAut.one_apply]
      map_mul' := by
        intro a b
        apply MulEquiv.ext
        intro x
        induction x using QuotientGroup.induction_on
        simp only [QuotientGroup.congr_mk, map_mul, MulAut.mul_apply] }
  have hker : CFSG.pCore 2 ↥H ≤ ρ₁.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x fun e => ?_
    change QuotientGroup.congr K K (ρH q) (hmap q) (QuotientGroup.mk e) =
      (1 : MulAut (↥E ⧸ K)) (QuotientGroup.mk e)
    rw [QuotientGroup.congr_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem,
      Subgroup.mem_subgroupOf]
    have hcoe : (((ρH q e : ↥E) / e : ↥E) : Γ) =
        (q : Γ) * (e : Γ) * (q : Γ)⁻¹ * (e : Γ)⁻¹ := by
      rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, hρH]
    rw [hcoe]
    exact hQ q hq (e : Γ) e.2
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥H) ρ₁ hker, fun h e e' he => ?_⟩
  change QuotientGroup.congr K K (ρH h) (hmap h) (QuotientGroup.mk e) = QuotientGroup.mk e'
  rw [QuotientGroup.congr_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext (by rw [hρH, he]))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
