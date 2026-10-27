module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOmegaTwoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8SimOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.RankTwoClassical
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem s16k_fixNc_statedOmegaPlus_two_two [CharP K 2] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) : FixNc (StatedOmega (StatedQuadPlus m K)) 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 0 < k := by omega
  have hpK : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; norm_num
  obtain ⟨x, y, hxQ, hyQ, hxy, hox, hoy, hyx, hfix⟩ :=
    s16k_omega_blocks (p := 3) (plusOe k) (statedQuadPlus_plusOe k) Nat.prime_three hpK
  have hxΩ : x ∈ StatedOmega (StatedQuadPlus (k + 2) K) :=
    s16g_le_statedOmegaPlus_of_odd (by omega) Nat.prime_three (by norm_num)
      (E := Subgroup.zpowers x) (fun z hz => s16k_zpowers_pow_eq_one hox hz)
      (fun z hz v => s16k_isometry_of_mem_zpowers hxQ hz v) (Subgroup.mem_zpowers x)
  have hyΩ : y ∈ StatedOmega (StatedQuadPlus (k + 2) K) :=
    s16g_le_statedOmegaPlus_of_odd (by omega) Nat.prime_three (by norm_num)
      (E := Subgroup.zpowers y) (fun z hz => s16k_zpowers_pow_eq_one hoy hz)
      (fun z hz v => s16k_isometry_of_mem_zpowers hyQ hz v) (Subgroup.mem_zpowers y)
  let u : Fin (k + 2) ⊕ Fin (k + 2) → K := Pi.single (plusOe k (.inl (.inl ⟨0, hk⟩))) 1
  have hsupp : ∀ b, u (plusOe k (.inr b)) = 0 := fun b =>
    Pi.single_eq_of_ne ((plusOe k).injective.ne Sum.inr_ne_inl) _
  have hQu : StatedQuadPlus (k + 2) K u = 0 := by
    have h : ∀ i : Fin (k + 2), u (Sum.inr i) = 0 := fun i =>
      Pi.single_eq_of_ne Sum.inr_ne_inl _
    show ∑ i : Fin (k + 2), u (.inl i) * u (.inr i) = 0
    exact Finset.sum_eq_zero fun i _ => by rw [h i, mul_zero]
  have hfixu := hfix u hsupp
  exact s16g_fixNc_of_fixed_pair_singular (CFSG.LieType.Universal.Spin.quadPlus (k + 2) K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (k + 2) K) _
    Nat.prime_three (by norm_num)
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaPlus_exists_mulVec_eq (by omega) hx hy hxy)
    hxΩ hyΩ hxy hox hoy hyx (s16k_single_ne_zero_om _)
    (by rw [CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hQu) hfixu.1 hfixu.2

theorem s16k_fixNc_statedOmegaMinus_two_two [CharP K 2] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 4 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    FixNc (StatedOmega (StatedQuadMinus m K b c)) 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  have hj : 0 < j := by omega
  have hpK : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; norm_num
  obtain ⟨x, y, hxQ, hyQ, hxy, hox, hoy, hyx, hfix⟩ :=
    s16k_omega_blocks (p := 3) (minusOe j) (statedQuadMinus_minusOe j b c) Nat.prime_three hpK
  have hxΩ : x ∈ StatedOmega (StatedQuadMinus (j + 3) K b c) :=
    s16g_le_statedOmegaMinus_of_odd (m := j + 3) (by omega) hirr Nat.prime_three (by norm_num)
      (E := Subgroup.zpowers x) (fun z hz => s16k_zpowers_pow_eq_one hox hz)
      (fun z hz v => s16k_isometry_of_mem_zpowers hxQ hz v) (Subgroup.mem_zpowers x)
  have hyΩ : y ∈ StatedOmega (StatedQuadMinus (j + 3) K b c) :=
    s16g_le_statedOmegaMinus_of_odd (m := j + 3) (by omega) hirr Nat.prime_three (by norm_num)
      (E := Subgroup.zpowers y) (fun z hz => s16k_zpowers_pow_eq_one hoy hz)
      (fun z hz v => s16k_isometry_of_mem_zpowers hyQ hz v) (Subgroup.mem_zpowers y)
  let u : Fin (j + 2) ⊕ Fin (j + 2) ⊕ Fin 2 → K :=
    Pi.single (minusOe j (.inl (.inl ⟨0, hj⟩))) 1
  have hsupp : ∀ b, u (minusOe j (.inr b)) = 0 := fun b =>
    Pi.single_eq_of_ne ((minusOe j).injective.ne Sum.inr_ne_inl) _
  have hQu : StatedQuadMinus (j + 3) K b c u = 0 := by
    have h : ∀ i : Fin (j + 2) ⊕ Fin 2, u (Sum.inr i) = 0 := fun i =>
      Pi.single_eq_of_ne Sum.inr_ne_inl _
    show (∑ i : Fin (j + 2), u (.inl i) * u (.inr (.inl i))) + u (.inr (.inr 0)) ^ 2 +
      b * u (.inr (.inr 0)) * u (.inr (.inr 1)) + c * u (.inr (.inr 1)) ^ 2 = 0
    rw [h (.inr 0), h (.inr 1)]
    simp [h]
  have hfixu := hfix u hsupp
  exact s16g_fixNc_of_fixed_pair_singular (CFSG.LieType.Universal.Spin.quadMinus (j + 3) K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (j + 3) K hirr) _
    Nat.prime_three (by norm_num)
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq (by omega) hirr hx hy hxy)
    hxΩ hyΩ hxy hox hoy hyx (s16k_single_ne_zero_om _)
    (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hQu) hfixu.1 hfixu.2

theorem s16k_fixOrd_statedOmegaMinus_three_two [CharP K 2] (hK : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    FixOrd (StatedOmega (StatedQuadMinus 3 K b c)) 3 := by
  have hu₂ : StatedQuadMinus (0 + 1) K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) = 1 := by
    have h : ∀ v : Fin (0 + 1 - 1) ⊕ Fin (0 + 1 - 1) ⊕ Fin 2 → K,
        StatedQuadMinus (0 + 1) K b c v =
          (∑ i : Fin (0 + 1 - 1), v (.inl i) * v (.inr (.inl i))) + v (.inr (.inr 0)) ^ 2 +
            b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 :=
      fun v => rfl
    rw [h]
    simp
  have hpK : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; norm_num
  obtain ⟨g, hgQ, hg, u, hu, hQu, hfix⟩ := s16k_omega_fixed_singular (p := 3) (minusOe 0)
    (statedQuadMinus_minusOe 0 b c) Nat.prime_three hpK hu₂
  have hgΩ : g ∈ StatedOmega (StatedQuadMinus 3 K b c) :=
    s16g_le_statedOmegaMinus_of_odd (m := 3) (by norm_num) hirr Nat.prime_three (by norm_num)
      (E := Subgroup.zpowers g) (fun z hz => s16k_zpowers_pow_eq_one hg hz)
      (fun z hz v => s16k_isometry_of_mem_zpowers hgQ hz v) (Subgroup.mem_zpowers g)
  exact s16g_fixOrd_of_fixed_singular (CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr) _
    Nat.prime_three (by norm_num)
    (fun _ hA v => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.RankThree.GF2n.Smith81.Smith23E1.statedOmega_isometry _ hA v)
    (fun _ _ hx hy hxy =>
      CFSG.ClassicalGroups.Orthogonal.statedOmegaMinus_exists_mulVec_eq (by omega) hirr hx hy hxy)
    hgΩ hg hu (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hQu) hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
