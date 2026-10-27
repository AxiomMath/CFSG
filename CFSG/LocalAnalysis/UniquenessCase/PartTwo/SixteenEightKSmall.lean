module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Small
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)

variable {K : Type} [Field K] [Finite K]

private theorem s16k_commutator_comm_of_card {L : Type*} [Group L] {O : Subgroup L} {p k : ℕ}
    (hp : p.Prime) (hk : k = 1 ∨ k = 2) (hO : Nat.card O = 2 * p ^ k) :
    ∀ a ∈ ⁅O, O⁆, ∀ b ∈ ⁅O, O⁆, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  haveI : Finite O := Nat.finite_of_card_ne_zero (by rw [hO]; omega)
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := O) p (n := k)
    ⟨2, by rw [hO]; ring⟩
  have hidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hP, hO] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  haveI : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcomm : ∀ x y : P, x * y = y * x := by
    rcases hk with rfl | rfl
    · haveI := isCyclic_of_prime_card (hP.trans (pow_one p))
      exact fun x y => mul_comm' x y
    · haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP
      exact fun x y => mul_comm' x y
  have hQcard : Nat.card (O ⧸ P) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isCyclic_of_prime_card hQcard
  have hcomm : ∀ x y : O, ⁅x, y⁆ ∈ P := by
    intro x y
    have h : (QuotientGroup.mk' P) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' _ _)
    exact (QuotientGroup.eq_one_iff _).1 h
  have hle : ⁅O, O⁆ ≤ P.map O.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : O), ⟨y, hy⟩⁆, hcomm _ _, by simp [commutatorElement_def]⟩
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := hle ha
  obtain ⟨b', hb', rfl⟩ := hle hb
  exact congrArg (fun z : P => O.subtype z.1) (hPcomm ⟨a', ha'⟩ ⟨b', hb'⟩)

private theorem s16k_comm_statedOmega_of_card {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) {p k : ℕ}
    (hp : p.Prime) (hk : k = 1 ∨ k = 2)
    (hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * p ^ k) :
    ∀ x ∈ StatedOmega Q₀, ∀ y ∈ StatedOmega Q₀, x * y = y * x := by
  intro x hx y hy
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hx hy
  have h := s16k_commutator_comm_of_card hp hk hO _ hx _ hy
  exact (toLinEquiv ι K).injective (by
    rw [map_mul, map_mul]
    exact h)

private theorem s16k_comm_statedOmegaMinus_one_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ x ∈ StatedOmega (StatedQuadMinus 1 K b c), ∀ y ∈ StatedOmega (StatedQuadMinus 1 K b c),
      x * y = y * x := by
  refine s16k_comm_statedOmega_of_card (coe_quadMinus 1 K b c) (by norm_num : Nat.Prime 5)
    (Or.inl rfl) ?_
  have h : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (0 * (0 + 1)) * ((Nat.card K : ℤ) ^ (0 + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 0, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 0
  have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
      2 * 5 ^ 1 := by
    rw [h, hK]
    simp
  exact_mod_cast h2

private theorem s16k_comm_statedOmegaPlus_one_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∀ x ∈ StatedOmega (StatedQuadPlus 1 K), ∀ y ∈ StatedOmega (StatedQuadPlus 1 K),
      x * y = y * x := by
  refine s16k_comm_statedOmega_of_card (coe_quadPlus 1 K) Nat.prime_three (Or.inl rfl) ?_
  have h : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 1 K)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (0 * (0 + 1)) * ((Nat.card K : ℤ) ^ (0 + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 0, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := K) 0
  have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 1 K)) : ℤ) =
      2 * 3 ^ 1 := by
    rw [h, hK]
    simp
  exact_mod_cast h2

theorem s16k_comm_statedOmegaPlus_of_le_one_four (hK : Nat.card K = 4) {m : ℕ} (hm : m ≤ 1) :
    ∀ x ∈ StatedOmega (StatedQuadPlus m K), ∀ y ∈ StatedOmega (StatedQuadPlus m K),
      x * y = y * x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · intro x _ y _
    exact s16g_mul_comm_of_card_le_one (by simp) x y
  · exact s16k_comm_statedOmegaPlus_one_four hK

theorem s16k_comm_statedOmegaMinus_of_le_one_four (hK : Nat.card K = 4) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m ≤ 1) :
    ∀ x ∈ StatedOmega (StatedQuadMinus m K b c), ∀ y ∈ StatedOmega (StatedQuadMinus m K b c),
      x * y = y * x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact s16k_comm_statedOmegaMinus_one_four hK hirr
  · exact s16k_comm_statedOmegaMinus_one_four hK hirr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
