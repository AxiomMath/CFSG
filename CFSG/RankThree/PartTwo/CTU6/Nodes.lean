module

public import CFSG.RankThree.PartTwo.CTU6.RootElts

public section

namespace CFSG.RankThree.PartTwo.CTU6

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.WeakCT (blk blk_injective blk_zero_tv01 blk_zero_tv10
  blk_one_tv01 blk_one_tv10)
open CFSG.Timmesfeld (tv)
open scoped MatrixGroups

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

section Short

variable {n : ℕ} {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)

include hk in
theorem short_upper_mem (c : F) :
    rootHom σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
      (Multiplicative.ofAdd c) ∈ rootGroup σ hσ n (Pi.single k 1) :=
  rootHom_mem hσ _ _ _ (lowIdx_ne_rev _ _) (toStd_short hk).symm _

include hk in
theorem short_lower_mem (c : F) :
    rootHom σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev k k)
      (Multiplicative.ofAdd c) ∈ rootGroup σ hσ n (-Pi.single k 1) :=
  rootHom_mem hσ _ _ _ (lowIdx_ne_rev _ _) (toStd_short_neg hk).symm _

include hk in
theorem short_param_upper (r : SL(2, F) →* SU σ n)
    (hr : ∀ c, r (tv 0 1 c) = rootHom σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k)
      (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c)) :
    ∀ g ∈ rootGroup σ hσ n (Pi.single k 1), ∃ c, r (tv 0 1 c) = g := by
  intro g hg
  refine ⟨mat σ n g (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩), ?_⟩
  have hx := short_upper_mem hσ hk (mat σ n g (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩))
  rw [hr]
  refine eq_of_toBlock_short hk (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_left hg) ?_
  rw [toBlock_of_mem_pos hk hx, toBlock_of_mem_pos hk hg, mat_apply, coe_rootHom, toAdd_ofAdd,
    rootMatrix_apply_pq (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _)]

include hk in
theorem short_param_lower (r : SL(2, F) →* SU σ n)
    (hr : ∀ c, r (tv 1 0 c) = rootHom σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev k k) (Multiplicative.ofAdd c)) :
    ∀ g ∈ rootGroup σ hσ n (-Pi.single k 1), ∃ c, r (tv 1 0 c) = g := by
  intro g hg
  refine ⟨mat σ n g (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k), ?_⟩
  have hx := short_lower_mem hσ hk (mat σ n g (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k))
  rw [hr]
  refine eq_of_toBlock_short hk (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_right hg) ?_
  rw [toBlock_of_mem_neg hk hx, toBlock_of_mem_neg hk hg, mat_apply, coe_rootHom, toAdd_ofAdd,
    rootMatrix_apply_pq (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _)]

end Short

abbrev k0 : Fin (6 / 2) := ⟨0, by decide⟩

abbrev k1 : Fin (6 / 2) := ⟨1, by decide⟩

abbrev k2 : Fin (6 / 2) := ⟨2, by decide⟩

variable (σ) in
@[expose] noncomputable def rS0 : SL(2, F) →* SU σ 6 := (embSL3 σ hσ).comp (blk F 0)

variable (σ) in
@[expose] noncomputable def rS1 : SL(2, F) →* SU σ 6 := (embSL3 σ hσ).comp (blk F 1)

theorem rS0_injective : Function.Injective (rS0 σ hσ) :=
  (embSL3_injective σ hσ).comp (blk_injective 0)

theorem rS1_injective : Function.Injective (rS1 σ hσ) :=
  (embSL3_injective σ hσ).comp (blk_injective 1)

theorem rS0_tv01 (c : F) :
    rS0 σ hσ (tv 0 1 c) = rootHom σ hσ (lowIdx_ne_succ (k := k0) (by decide))
      (lowIdx_ne_rev k0 k0) (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c) := by
  rw [rS0, MonoidHom.comp_apply, blk_zero_tv01, embSL3_tv01]
  rfl

theorem rS0_tv10 (c : F) :
    rS0 σ hσ (tv 1 0 c) = rootHom σ hσ (lowIdx_ne_succ (k := k0) (by decide)).symm
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev k0 k0) (Multiplicative.ofAdd c) := by
  rw [rS0, MonoidHom.comp_apply, blk_zero_tv10, embSL3_tv10]
  rfl

theorem rS1_tv01 (c : F) :
    rS1 σ hσ (tv 0 1 c) = rootHom σ hσ (lowIdx_ne_succ (k := k1) (by decide))
      (lowIdx_ne_rev k1 k1) (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c) := by
  rw [rS1, MonoidHom.comp_apply, blk_one_tv01, embSL3_tv12]
  rfl

theorem rS1_tv10 (c : F) :
    rS1 σ hσ (tv 1 0 c) = rootHom σ hσ (lowIdx_ne_succ (k := k1) (by decide)).symm
      (lowIdx_ne_rev _ _) (lowIdx_ne_rev k1 k1) (Multiplicative.ofAdd c) := by
  rw [rS1, MonoidHom.comp_apply, blk_one_tv10, embSL3_tv21]
  rfl

end CFSG.RankThree.PartTwo.CTU6
