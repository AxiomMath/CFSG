module

public import CFSG.LocalAnalysis.ZStar.PrincipalRegularPower
public import CFSG.LocalAnalysis.ZStar.TransferReduction

public section

namespace CFSG

namespace ZStar.RegularIdempotent

open ZStar.Helpers
open ZStar.BrauerBlockLift
open ZStar.BrauerPrincipal
open ZStar.BrauerProjection
open ZStar.PrincipalRegularPower
open ZStar.TransferReduction

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

private theorem odd_orderOf_mul_of_mem_odd_normal
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (n : N) {x : G} (hx : Odd (orderOf x)) :
    Odd (orderOf ((n : G) * x)) := by
  let K : Subgroup G := Subgroup.zpowers x
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.card_zpowers]
    exact hx
  have hsupodd : Odd (Nat.card ↥(N ⊔ K)) :=
    odd_card_sup_of_le_normalizer
      (A := N) (B := K) Subgroup.le_normalizer_of_normal hNodd hKodd
  apply hsupodd.of_dvd_nat
  apply (N ⊔ K).orderOf_dvd_natCard
  exact (N ⊔ K).mul_mem
    ((show N ≤ N ⊔ K from le_sup_left) n.property)
    ((show K ≤ N ⊔ K from le_sup_right) (Subgroup.mem_zpowers x))

private theorem odd_orderOf_mul_iff_of_mem_odd_normal
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (n : N) (x : G) :
    Odd (orderOf ((n : G) * x)) ↔ Odd (orderOf x) := by
  constructor
  · intro hx
    have h := odd_orderOf_mul_of_mem_odd_normal N hNodd
      (⟨(n : G)⁻¹, N.inv_mem n.property⟩ : N) hx
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
  · exact odd_orderOf_mul_of_mem_odd_normal N hNodd n

private theorem single_mul_twoRegularSum_of_mem_odd_normal
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (n : N) :
    MonoidAlgebra.single (n : G) 1 * twoRegularSum G = twoRegularSum G := by
  classical
  unfold twoRegularSum
  rw [Finset.mul_sum]
  let F : G → GroupAlgebraTwo G := fun x ↦
    if Odd (orderOf x) then MonoidAlgebra.single x 1 else 0
  calc
    (∑ x : G,
        MonoidAlgebra.single (n : G) (1 : ZMod 2) *
          (if Odd (orderOf x) then
            MonoidAlgebra.single x (1 : ZMod 2) else 0)) =
        ∑ x : G, F ((n : G) * x) := by
      apply Finset.sum_congr rfl
      intro x _
      have hiff := odd_orderOf_mul_iff_of_mem_odd_normal N hNodd n x
      by_cases hx : Odd (orderOf x)
      · simp [F, hx, hiff.mpr hx]
      · have hnx : ¬ Odd (orderOf ((n : G) * x)) :=
          fun h ↦ hx (hiff.mp h)
        simp [F, hx, hnx]
    _ = ∑ x : G, F x := Equiv.sum_comp (Equiv.mulLeft (n : G)) F
    _ = ∑ x : G,
          (if Odd (orderOf x) then
            MonoidAlgebra.single x (1 : ZMod 2) else 0) := rfl

private theorem single_mul_twoRegularSum_pow_of_mem_odd_normal
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (n : N)
    {k : ℕ} (hk : k ≠ 0) :
    MonoidAlgebra.single (n : G) 1 * (twoRegularSum G) ^ k =
      (twoRegularSum G) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ']
  calc
    MonoidAlgebra.single (n : G) 1 *
        (twoRegularSum G * (twoRegularSum G) ^ j) =
      (MonoidAlgebra.single (n : G) 1 * twoRegularSum G) *
        (twoRegularSum G) ^ j := by rw [mul_assoc]
    _ = twoRegularSum G * (twoRegularSum G) ^ j := by
      rw [single_mul_twoRegularSum_of_mem_odd_normal N hNodd n]

private noncomputable def regularIdempotentPowerData
    (X : Type*) [Group X] [Fintype X] :
    {n : ℕ // n ≠ 0 ∧
      (twoRegularSum X) ^ n * (twoRegularSum X) ^ n =
        (twoRegularSum X) ^ n} := by
  classical
  letI : Fintype (GroupAlgebraTwo X) :=
    Fintype.ofEquiv (X →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  let h := exists_positive_idempotent_power (twoRegularSum X)
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

private noncomputable def regularIdempotentExponent
    (X : Type*) [Group X] [Fintype X] : ℕ :=
  (regularIdempotentPowerData X).1

private theorem regularIdempotentExponent_ne_zero
    (X : Type*) [Group X] [Fintype X] :
    regularIdempotentExponent X ≠ 0 :=
  (regularIdempotentPowerData X).2.1

noncomputable def regularIdempotent
    (X : Type*) [Group X] [Fintype X] : GroupAlgebraTwo X :=
  (twoRegularSum X) ^ regularIdempotentExponent X

theorem regularIdempotent_idempotent
    (X : Type*) [Group X] [Fintype X] :
    regularIdempotent X * regularIdempotent X = regularIdempotent X :=
  (regularIdempotentPowerData X).2.2

theorem regularIdempotent_central
    (X : Type*) [Group X] [Fintype X] :
    IsGroupCentral X (regularIdempotent X) :=
  isGroupCentral_pow (twoRegularSum X) (twoRegularSum_central X) _

theorem regularIdempotent_augmentation
    (X : Type*) [Group X] [Fintype X] :
    augmentationHom X (regularIdempotent X) = 1 := by
  rw [regularIdempotent, map_pow, augmentation_twoRegularSum, one_pow]

theorem single_mul_regularIdempotent_of_mem_odd_normal
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N)) (n : N) :
    MonoidAlgebra.single (n : G) 1 * regularIdempotent G =
      regularIdempotent G := by
  exact single_mul_twoRegularSum_pow_of_mem_odd_normal N hNodd n
    (regularIdempotentExponent_ne_zero G)

private theorem idempotent_positive_powers_eq
    {M : Type*} [Monoid M] (a : M) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (him : a ^ m * a ^ m = a ^ m)
    (hin : a ^ n * a ^ n = a ^ n) :
    a ^ m = a ^ n := by
  calc
    a ^ m = (a ^ m) ^ n :=
      (IsIdempotentElem.pow_eq him hn).symm
    _ = a ^ (m * n) := (pow_mul a m n).symm
    _ = a ^ (n * m) := by rw [Nat.mul_comm]
    _ = (a ^ n) ^ m := pow_mul a n m
    _ = a ^ n := IsIdempotentElem.pow_eq hin hm

theorem brauerProjection_regularIdempotent
    (w : G) (hw2 : w * w = 1) :
    brauerProjection w (regularIdempotent G) =
      regularIdempotent (involutionCentralizer w) := by
  let n := regularIdempotentExponent G
  let m := regularIdempotentExponent (involutionCentralizer w)
  have hn : n ≠ 0 := regularIdempotentExponent_ne_zero G
  have hm : m ≠ 0 :=
    regularIdempotentExponent_ne_zero (involutionCentralizer w)
  have hproj :
      brauerProjection w (regularIdempotent G) =
        (twoRegularSum (involutionCentralizer w)) ^ n := by
    calc
      brauerProjection w (regularIdempotent G) =
          (brauerProjection w (twoRegularSum G)) ^ n := by
        exact brauerProjection_pow w hw2 (twoRegularSum G)
          (twoRegularSum_central G) n
      _ = (twoRegularSum (involutionCentralizer w)) ^ n := by
        rw [brauerProjection_twoRegularSum]
  have hnidem :
      (twoRegularSum (involutionCentralizer w)) ^ n *
          (twoRegularSum (involutionCentralizer w)) ^ n =
        (twoRegularSum (involutionCentralizer w)) ^ n := by
    rw [← hproj]
    exact (brauerProjection_central_idempotent w hw2
      (regularIdempotent G) (regularIdempotent_central G)
      (regularIdempotent_idempotent G)).2
  have hmidem :
      (twoRegularSum (involutionCentralizer w)) ^ m *
          (twoRegularSum (involutionCentralizer w)) ^ m =
        (twoRegularSum (involutionCentralizer w)) ^ m := by
    exact regularIdempotent_idempotent (involutionCentralizer w)
  rw [hproj, regularIdempotent]
  exact idempotent_positive_powers_eq
    (twoRegularSum (involutionCentralizer w)) hn hm hnidem hmidem

end

end ZStar.RegularIdempotent

end CFSG
