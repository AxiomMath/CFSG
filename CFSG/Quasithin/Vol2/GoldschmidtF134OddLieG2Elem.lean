module

public import CFSG.LieType.Chevalley.G2Rank
public import CFSG.LieType.Chevalley.MinimalBorelOvergroups

set_option linter.unusedSectionVars false

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.Quasithin.H13.NQCore.G2


variable {τ : Tag} {K : Type} [Field K]

theorem coe_rootHom_mem_posUnipotent (β : Root τ) (hβ : 0 < height β.1) (c : Multiplicative K) :
    ((rootHom β c : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K := by
  have h1 := (rootOperatorFamily τ).eltElement_mem_rootSubgroup (K := K) β c.toAdd
  rw [← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K β, Subgroup.mem_subgroupOf] at h1
  have h2 : rootSubgroup τ K β.1 ≤ posUnipotent τ K := by
    rw [← rootSpan_singleton]
    exact rootSpan_le_posUnipotent fun α hα => by
      rw [Set.mem_singleton_iff] at hα
      subst hα
      exact ⟨β.2, hβ⟩
  exact h2 h1

theorem height_pos_g2 : 0 < height g2r12.1 ∧ 0 < height g2r13.1 ∧ 0 < height g2r23.1 := by
  have h : ∀ β ∈ wordRoots g2LongWord, 0 < height β.1 := fun β hβ =>
    (wordRoots_spec g2LongWord isReduced_G2_alternating β hβ).1
  rw [wordRoots_g2LongWord] at h
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩

section Elem

variable [Finite K] [CharP K 2]

theorem exists_elementaryAbelian_posUnipotent :
    ∃ E : Subgroup (adjointGroup .G2 K), (∀ x ∈ E, ((x : adjointGroup .G2 K) : ModGL .G2 K) ∈
      posUnipotent .G2 K) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = Nat.card K ^ 3 := by
  refine ⟨g2RootProd.range, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨a, b, c⟩, rfl⟩
    rw [g2RootProd_apply]
    simp only [Subgroup.coe_mul]
    obtain ⟨h12, h13, h23⟩ := height_pos_g2
    exact mul_mem (coe_rootHom_mem_posUnipotent _ h13 a) (mul_mem
      (coe_rootHom_mem_posUnipotent _ h12 b) (coe_rootHom_mem_posUnipotent _ h23 c))
  · rintro _ ⟨z, rfl⟩
    have hx : ∀ w : Multiplicative K, w ^ 2 = 1 := fun w => by
      change Multiplicative.ofAdd (2 • Multiplicative.toAdd w) = 1
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl
    rw [← map_pow]
    obtain ⟨a, b, c⟩ := z
    rw [Prod.pow_def, Prod.pow_def, hx, hx, hx]
    exact map_one _
  · rw [Nat.card_congr (MonoidHom.ofInjective g2RootProd_injective).toEquiv.symm, Nat.card_prod,
      Nat.card_prod, show Nat.card (Multiplicative K) = Nat.card K from
        Nat.card_congr Multiplicative.toAdd]
    ring

end Elem

end CFSG.Quasithin.H13.NQCore.G2
