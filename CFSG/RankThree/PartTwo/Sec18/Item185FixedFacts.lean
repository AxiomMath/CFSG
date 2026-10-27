module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterLin

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem fixedFactsAt_of_simple {S : Type} [Group S] {σ : MulAut S}
    (hs : IsSimpleGroup (fixedSubgroup σ)) (hna : ¬ ∀ x y : fixedSubgroup σ, x * y = y * x) :
    FixedFactsAt σ := by
  haveI := hs
  unfold FixedFactsAt
  left
  refine ⟨⊤, inferInstance, Subgroup.topEquiv.isSimpleGroup, ?_, ?_⟩
  · intro hc
    exact hna fun x y => congrArg Subtype.val (hc ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩)
  · rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (fixedSubgroup σ)) with
      h0 | h0
    · exact h0
    · refine absurd (fun x y => ?_) hna
      have hy : y ∈ Subgroup.center (fixedSubgroup σ) := by
        rw [h0]
        exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x

theorem fixedFactsAt_of_normal {S : Type} [Group S] {σ : MulAut S} {P : Subgroup S}
    (hPC : P ≤ fixedSubgroup σ)
    (hcomm : ∀ a : S, a ∈ fixedSubgroup σ → ∀ b : S, b ∈ fixedSubgroup σ → ⁅a, b⁆ ∈ P)
    (hs : IsSimpleGroup P) (hna : ¬ ∀ x y : P, x * y = y * x)
    (hcent : ∀ x ∈ fixedSubgroup σ, (∀ y ∈ P, x * y = y * x) → x = 1) : FixedFactsAt σ := by
  unfold FixedFactsAt
  left
  refine ⟨P.subgroupOf (fixedSubgroup σ), ⟨fun n hn g => ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgn : ((g * n * g⁻¹ : fixedSubgroup σ) : S) = ⁅(g : S), (n : S)⁆ * (n : S) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [hgn]
    exact P.mul_mem (hcomm _ g.2 _ n.2) hn
  · haveI := hs
    exact (Subgroup.subgroupOfEquivOfLe hPC).isSimpleGroup
  · intro hc
    apply hna
    intro x y
    have hxy := hc ⟨⟨x, hPC x.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
      ⟨⟨y, hPC y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
    exact Subtype.ext (congrArg (fun z : P.subgroupOf (fixedSubgroup σ) =>
      ((z : fixedSubgroup σ) : S)) hxy)
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_centralizer_iff] at hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hcent z z.2 fun y hy => ?_
    have hyz := hz ⟨y, hPC hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
    exact (congrArg Subtype.val hyz).symm

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
