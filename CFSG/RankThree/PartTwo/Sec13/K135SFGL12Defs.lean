module

public import CFSG.RankThree.PartTwo.Sec13.K135SFDefs
public import CFSG.RankThree.PartTwo.Sec13.K135G1Out

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG Subgroup CFSG.RankThree.PartTwo.Sec13.F135Last
open scoped commutatorElement

@[expose] def KFactMultPrimeGL12 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q → CFSG.IsKGroup (Q ⧸ Subgroup.center Q) →
    GL12Data (Q ⧸ Subgroup.center Q) →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ¬ p ∣ Nat.card (Subgroup.center Q)

@[expose] def KFactOutGL12 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.IsKGroup S → IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    GL12Data S → ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ f : MulAut S, orderOf f = p → f ∈ (MulAut.conj : S →* MulAut S).range

@[expose] def KF135GL12 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.IsKGroup S → IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    GL12Data S → ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ P : Subgroup (MulAut S), IsPGroup p P → p ^ 3 ≤ Nat.card P → (∀ x ∈ P, x ^ p = 1) →
    (∀ F : Subgroup (MulAut S), F ≤ (MulAut.conj : S →* MulAut S).range →
        CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
        ∀ T : Subgroup S, T ≠ ⊥ → IsPGroup 2 T → ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T) →
    False

@[expose] def KFactG1GL12 : Prop :=
  ∀ (I : Type) [Group I] [Finite I], CFSG.IsQuasisimple I →
    CFSG.IsKGroup (I ⧸ Subgroup.center I) → GL12Data (I ⧸ Subgroup.center I) →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ f : MulAut I, orderOf f = p →
      ∀ V : Subgroup (MulAut (I ⧸ Subgroup.center I)), V ≠ ⊥ → IsPGroup 2 V →
        (∀ v ∈ V, (centerQuotMulAut I f) * v * (centerQuotMulAut I f)⁻¹ ∈ V) →
        ⁅V, Subgroup.zpowers (centerQuotMulAut I f)⁆ = V →
        ∃ T : Subgroup I, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map f.toMonoidHom = T

private theorem mulAut_mul_conj_mul_inv {S : Type*} [Group S] (α : MulAut S) (g : S) :
    α * (MulAut.conj g : MulAut S) * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem kFactG1GL12_of_outGL12 (hO : KFactOutGL12) : KFactG1GL12 := by
  intro I _ _ hQ hK hGL p hp hp7 f hf V hV1 hV2 hVn hVc
  haveI : Fact p.Prime := ⟨hp⟩
  refine g1o_lift_of_V_le_inn hQ f V hV1 hV2 hVn ?_
  have hfp : f ^ p = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf] at this
  have hfb : centerQuotMulAut I f ∈ (MulAut.conj : (I ⧸ Subgroup.center I) →*
      MulAut (I ⧸ Subgroup.center I)).range := by
    by_cases h : centerQuotMulAut I f = 1
    · rw [h]
      exact Subgroup.one_mem _
    · refine hO _ hK hQ.2.1 hQ.2.2 hGL p hp hp7 _ (orderOf_eq_prime ?_ h)
      rw [← map_pow, hfp, map_one]
  refine hVc.ge.trans ?_
  rw [Subgroup.commutator_le]
  intro v _ s hs
  obtain ⟨g, rfl⟩ := (Subgroup.zpowers_le.mpr hfb) hs
  refine ⟨v g * g⁻¹, ?_⟩
  rw [map_mul, map_inv, commutatorElement_def, ← mulAut_mul_conj_mul_inv v g]

end CFSG.RankThree.PartTwo.Sec13.K135SF
