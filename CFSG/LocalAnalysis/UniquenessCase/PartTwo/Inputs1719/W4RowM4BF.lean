module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4BFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4HeisCard
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNF
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BRank0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Blueprint CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.LinearAlgebra.F2Cube
  CFSG.HardMathSupport.Solomon.Coordinator.B3B

theorem m4_bThree_classification_B :
    ∀ s : NativeSporadic.B, orderOf s = 3 → rk s = 2862 ∨ IsConj s (phiB (t3 1)) := by
  intro s hs
  obtain ⟨i, hi⟩ := bThree_classes s hs
  have e0 : ∀ {r : NativeSporadic.B}, IsConj r (phiB (t3 0)) → rk r = 2862 := fun {r} hc => by
    have h : rk r = rk (phiB (t3 0)) := CFSG.Monster.Existence.rank_sub_one_of_isConj hc
    rw [h, rk_phiB_t3_zero]
  fin_cases i
  · exact Or.inl (e0 hi)
  · exact Or.inr hi
  · exact Or.inl (e0 (hi.trans bThreeRc_holds))
  · exact Or.inr (hi.trans bThreeRd_holds)

theorem exists_noncentral_isConj_centre_B :
    ∃ (x y : Fin 4 → NativeSporadic.B) (z u : NativeSporadic.B),
      HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) ∧ u ∉ Subgroup.zpowers z ∧
        IsConj u z := by
  classical
  obtain ⟨x, y, z, g, hcfg, hy, -, -, -, hrkz⟩ := bNF_holds
  refine ⟨x, y, z, ?_⟩
  set Q : Subgroup NativeSporadic.B :=
    Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) with hQ
  set H : Subgroup NativeSporadic.B := heisSub x y z with hH
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : orderOf z = 3 := orderOf_eq_prime hcfg.zp hcfg.z1
  have hconjz : IsConj z (phiB (t3 1)) := by
    rcases m4_bThree_classification_B z hz3 with h | h
    · rw [hrkz] at h
      exact absurd h (by norm_num)
    · exact h
  have hHcard : Nat.card H = 3 ^ 6 := by
    rw [hH]
    exact card_heisSub hcfg hy
  have hpow : ∀ g : H, (g : NativeSporadic.B) ^ 3 = 1 :=
    fun g => pow_three_eq_one_of_mem_heisSub hcfg hy g.2
  have hHQ : H ≤ Q := by
    rw [hH, hQ]
    exact heisSub_le_closure x y z
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hHcard]; norm_num)
  haveI : Fintype H := Fintype.ofFinite H
  have hHfcard : Fintype.card H = 3 ^ 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact hHcard
  have hzH : z ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (Set.mem_insert z _)
  set a : H := ⟨z, hzH⟩ with ha
  have haz : (a : NativeSporadic.B) = z := by rw [ha]
  have hord_a : orderOf a = 3 := by
    have h := orderOf_injective (Subgroup.subtype H) Subtype.val_injective a
    rw [← h]
    change orderOf (a : NativeSporadic.B) = 3
    rw [haz]
    exact hz3
  have ha1 : a ≠ 1 := by
    intro h1
    have h : orderOf a = 1 := by rw [h1]; exact orderOf_one
    rw [hord_a] at h
    exact absurd h (by norm_num)
  have ha2 : a ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hord_a] at hdvd
    rcases hdvd with ⟨k, hk⟩
    omega
  have haa : a ≠ a ^ 2 := by
    intro h
    have h1 : a = 1 := by
      calc a = a ^ 2 * a⁻¹ := by group
        _ = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel a
    exact ha1 h1
  have key : ∃ u : NativeSporadic.B, u ∈ Q ∧ u ∉ Subgroup.zpowers z ∧ IsConj u z := by
    by_contra hno
    have hkey : ∀ h : H, (h : NativeSporadic.B) ∉ Subgroup.zpowers z →
        rk (h : NativeSporadic.B) = 2862 := by
      intro h hh
      have hh3 : (h : NativeSporadic.B) ^ 3 = 1 := hpow h
      have hh1 : (h : NativeSporadic.B) ≠ 1 := by
        intro h1
        exact hh (by rw [h1]; exact Subgroup.one_mem _)
      have hord : orderOf (h : NativeSporadic.B) = 3 := orderOf_eq_prime hh3 hh1
      rcases m4_bThree_classification_B (h : NativeSporadic.B) hord with h2862 | hconj
      · exact h2862
      · exact absurd (hconj.trans hconjz.symm)
          (fun hc => hno ⟨(h : NativeSporadic.B), hHQ h.2, hh, hc⟩)
    have hf_1 : fixedCount (((1 : H) : NativeSporadic.B).val.val) = 2 ^ 4370 := by
      rw [fixedCount_B_eq]
      have h1 : rk ((1 : H) : NativeSporadic.B) = 0 := by
        show rk (1 : NativeSporadic.B) = 0
        simp [rk]
      rw [h1]
    have hf_a : fixedCount ((a : NativeSporadic.B).val.val) = 2 ^ 1454 := by
      rw [fixedCount_B_eq]
      have h1 : rk (a : NativeSporadic.B) = 2916 := by rw [haz]; exact hrkz
      rw [h1]
    have hf_a2 : fixedCount (((a ^ 2 : H) : NativeSporadic.B).val.val) = 2 ^ 1454 := by
      rw [fixedCount_B_eq]
      have h2 : rk ((a ^ 2 : H) : NativeSporadic.B) = 2916 := by
        change rk ((a : NativeSporadic.B) ^ 2) = 2916
        have hcop : Nat.Coprime 2 (orderOf (a : NativeSporadic.B)) := by
          rw [haz, hz3]
          norm_num
        rw [rk_pow_eq_of_coprime hcop]
        rw [haz]
        exact hrkz
      rw [h2]
    have hf_out : ∀ h : H, (h : NativeSporadic.B) ∉ Subgroup.zpowers z →
        fixedCount ((h : NativeSporadic.B).val.val) = 2 ^ 1508 := by
      intro h hh
      rw [fixedCount_B_eq, hkey h hh]
    have hfilter : (Finset.univ.filter (fun h : H =>
        (h : NativeSporadic.B) ∈ Subgroup.zpowers z)) = ({1, a, a ^ 2} : Finset H) := by
      apply Finset.ext
      intro h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        set m : ℤ := k % ((3 : ℕ) : ℤ) with hm
        have hk3 : z ^ m = (h : NativeSporadic.B) := by
          have h := zpow_mod_orderOf z k
          rw [hz3, ← hm] at h
          exact h.trans hk
        have hm0 : 0 ≤ m := by rw [hm]; exact Int.emod_nonneg k (by norm_num)
        have hm3 : m < 3 := by rw [hm]; exact Int.emod_lt_of_pos k (by norm_num)
        have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hcases with h0 | h1 | h2
        · left
          have hv : (h : NativeSporadic.B) = 1 := by rw [← hk3, h0]; simp
          exact Subtype.ext hv
        · right; left
          have hv : (h : NativeSporadic.B) = z := by rw [← hk3, h1]; norm_num
          exact Subtype.ext hv
        · right; right
          have hv : (h : NativeSporadic.B) = z ^ 2 := by rw [← hk3, h2]; norm_num
          refine Subtype.ext ?_
          rw [hv]
          rfl
      · intro hh
        rcases hh with rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers z
        · exact pow_mem (Subgroup.mem_zpowers z) 2
    have hsum_in : (Finset.univ.filter (fun h : H =>
        (h : NativeSporadic.B) ∈ Subgroup.zpowers z)).sum
        (fun h : H => fixedCount ((h : NativeSporadic.B).val.val))
        = 2 ^ 4370 + 2 * 2 ^ 1454 := by
      rw [hfilter]
      rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨ha1.symm, ha2.symm⟩),
          Finset.sum_insert (by
            simp only [Finset.mem_singleton]
            exact haa),
          Finset.sum_singleton]
      rw [hf_1, hf_a, hf_a2, two_mul]
    have hcard_out : (Finset.univ.filter (fun h : H =>
        ¬ (h : NativeSporadic.B) ∈ Subgroup.zpowers z)).card = 726 := by
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset H))
        (p := fun h : H => (h : NativeSporadic.B) ∈ Subgroup.zpowers z)
      rw [Finset.card_univ, hHfcard] at htot
      have hp3 : (Finset.univ.filter (fun h : H =>
          (h : NativeSporadic.B) ∈ Subgroup.zpowers z)).card = 3 := by
        rw [hfilter]
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨ha1.symm, ha2.symm⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact haa),
            Finset.card_singleton]
      omega
    have hsum_out : (Finset.univ.filter (fun h : H =>
        ¬ (h : NativeSporadic.B) ∈ Subgroup.zpowers z)).sum
        (fun h : H => fixedCount ((h : NativeSporadic.B).val.val))
        = 726 * 2 ^ 1508 := by
      rw [show (726 : ℕ) = (Finset.univ.filter (fun h : H =>
          ¬ (h : NativeSporadic.B) ∈ Subgroup.zpowers z)).card from hcard_out.symm]
      exact Finset.sum_const_nat (fun h hh => hf_out h (by simpa using hh))
    have hsum : (Finset.univ.sum (fun h : H =>
        fixedCount ((h : NativeSporadic.B).val.val)))
        = 2 ^ 4370 + 2 * 2 ^ 1454 + 726 * 2 ^ 1508 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset H))
        (p := fun h : H => (h : NativeSporadic.B) ∈ Subgroup.zpowers z)
        (f := fun h : H => fixedCount ((h : NativeSporadic.B).val.val))]
      rw [hsum_in, hsum_out]
    have hdvd : (3 : ℕ) ^ 6 ∣ 2 ^ 4370 + 2 * 2 ^ 1454 + 726 * 2 ^ 1508 := by
      have h := card_dvd_sum_fixedCount_B H
      rwa [hHfcard, hsum] at h
    have hdvd729 : 729 ∣ 2 ^ 4370 + 2 * 2 ^ 1454 + 726 * 2 ^ 1508 := by
      have h := hdvd
      rwa [show (3 : ℕ) ^ 6 = 729 by norm_num] at h
    have hmod : (2 ^ 4370 + 2 * 2 ^ 1454 + 726 * 2 ^ 1508) % 729 = 486 := by
      decide +kernel
    have hzero : (2 ^ 4370 + 2 * 2 ^ 1454 + 726 * 2 ^ 1508) % 729 = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd729
    omega
  obtain ⟨u, huQ, huz, hconj⟩ := key
  exact ⟨u, hcfg, hy, huQ, huz, hconj⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
