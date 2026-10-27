module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourRed

public section

namespace CFSG.StandardType.SpFour

open Module CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpFull CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] {m : ℕ}

theorem blocks_of_order_three [Finite K] (hK : Nat.card K = 2) (hm : 1 ≤ m) {x : StatedSp m K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : SpPrimaryBlocks 2 1 3 x (proj m K x) := by
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hordp : orderOf (proj m K x) = 3 := by
    rw [orderOf_injective (proj m K) (proj_injective_sp (f := 1) (by rw [hK, pow_one]) le_rfl hm)
      x]
    exact hord
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := 1)
    (p := 3) Nat.prime_two le_rfl (by rw [hK, pow_one]) Nat.prime_three (by norm_num)
    (by norm_num) hm (proj m K x) hordp
  exact hblocks x rfl hord

theorem spEnd_inv_spEnd (g : StatedSp m K) (v : Fin m ⊕ Fin m → K) :
    spEnd g⁻¹ (spEnd g v) = v := by
  rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]

theorem spEnd_spEnd_inv' (g : StatedSp m K) (v : Fin m ⊕ Fin m → K) :
    spEnd g (spEnd g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply]

section Gamma

@[expose] def gammaT (T : Submodule K (Fin m ⊕ Fin m → K)) : Subgroup (StatedSp m K) where
  carrier := {g | (∀ v, spEnd g v - v ∈ T) ∧ ∀ t ∈ T, spEnd g t = t}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v => ?_, fun t ht => ?_⟩
    · have h1 : spEnd a (spEnd b v) = spEnd a (spEnd b v - v) + spEnd a v := by
        rw [map_sub]
        abel
      rw [spEnd_mul, Module.End.mul_apply, h1, ha2 _ (hb1 v)]
      have h2 := T.add_mem (hb1 v) (ha1 v)
      convert h2 using 1
      abel
    · rw [spEnd_mul, Module.End.mul_apply, hb2 t ht, ha2 t ht]
  one_mem' := by
    refine ⟨fun v => ?_, fun t _ => ?_⟩
    · rw [spEnd_one, Module.End.one_apply, sub_self]
      exact T.zero_mem
    · rw [spEnd_one, Module.End.one_apply]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ∀ t ∈ T, spEnd g⁻¹ t = t := fun t ht => by
      have := spEnd_inv_spEnd g t
      rwa [hg2 t ht] at this
    refine ⟨fun v => ?_, hinv⟩
    have hmem : v - spEnd g v ∈ T := by
      have := T.neg_mem (hg1 v)
      rwa [neg_sub] at this
    have h2 := hinv _ hmem
    rw [map_sub, spEnd_inv_spEnd] at h2
    rw [h2]
    exact hmem

variable [CharP K 2]

theorem gammaT_sq (T : Submodule K (Fin m ⊕ Fin m → K)) {g : StatedSp m K}
    (hg : g ∈ gammaT T) : g * g = 1 := by
  apply spEnd_injective
  refine LinearMap.ext fun v => ?_
  rw [spEnd_mul, Module.End.mul_apply, spEnd_one, Module.End.one_apply]
  have h1 : spEnd g (spEnd g v) = spEnd g (spEnd g v - v) + spEnd g v := by
    rw [map_sub]
    abel
  rw [h1, hg.2 _ (hg.1 v)]
  have h2 : spEnd g v + spEnd g v = 0 := SpFin.add_self_eq_zero_mod K _
  have h3 : v + v = 0 := SpFin.add_self_eq_zero_mod K _
  calc spEnd g v - v + spEnd g v = (spEnd g v + spEnd g v) - v := by abel
    _ = 0 - v := by rw [h2]
    _ = v := by rw [zero_sub]; exact neg_eq_of_add_eq_zero_right h3

theorem isPGroup_gammaT (T : Submodule K (Fin m ⊕ Fin m → K)) : IsPGroup 2 (gammaT T) := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  exact Subtype.ext (gammaT_sq T g.2)

theorem conj_mem_gammaT {T : Submodule K (Fin m ⊕ Fin m → K)} {a g : StatedSp m K}
    (ha : ∀ t ∈ T, spEnd a t ∈ T) (ha' : ∀ t ∈ T, spEnd a⁻¹ t ∈ T) (hg : g ∈ gammaT T) :
    a * g * a⁻¹ ∈ gammaT T := by
  refine ⟨fun v => ?_, fun t ht => ?_⟩
  · rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply]
    have h2 : spEnd a (spEnd g (spEnd a⁻¹ v)) - v =
        spEnd a (spEnd g (spEnd a⁻¹ v) - spEnd a⁻¹ v) := by
      rw [map_sub, spEnd_spEnd_inv']
    rw [h2]
    exact ha _ (hg.1 _)
  · rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply, hg.2 _ (ha' t ht),
      spEnd_spEnd_inv']

theorem spTransvection_mem_gammaT {T : Submodule K (Fin m ⊕ Fin m → K)}
    (hT : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0) {w : Fin m ⊕ Fin m → K} (hw : w ∈ T) (c : K) :
    spTransvection w c ∈ gammaT T := by
  refine ⟨fun v => ?_, fun t ht => ?_⟩
  · rw [spEnd_spTransvection, add_sub_cancel_left]
    exact T.smul_mem _ hw
  · rw [spEnd_spTransvection, hT t ht w hw, mul_zero, zero_smul, add_zero]

theorem spTransvection_ne_one' {w : Fin m ⊕ Fin m → K} (hw : w ≠ 0) :
    spTransvection w (1 : K) ≠ 1 := by
  obtain ⟨v, hv⟩ : ∃ v, spForm m K w v ≠ 0 := by
    by_contra h
    push Not at h
    exact hw ((spForm_nondegenerate (r := m) (K := K)).1 w h)
  exact spTransvection_ne_one hv

end Gamma


end CFSG.StandardType.SpFour
