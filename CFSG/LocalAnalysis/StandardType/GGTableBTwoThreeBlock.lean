module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvdBlock
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.StandardType.TwoThree

open Matrix CFSG.RankThree.CALinearPlane
open scoped commutatorElement

variable {m : ℕ} {K : Type} [Field K]

theorem fin_zero_ne_one' : (0 : Fin (m + 2)) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem fin_one_ne_zero' : (1 : Fin (m + 2)) ≠ 0 := fun h => fin_zero_ne_one' h.symm

variable (m K) in
@[expose] noncomputable def g0 : SpecialLinearGroup (Fin (m + 2)) K :=
  SpecialLinearGroup.transvection fin_zero_ne_one' 1 *
    SpecialLinearGroup.transvection fin_one_ne_zero' 1

variable [CharP K 2]

theorem coe_g0_apply (i k : Fin (m + 2)) :
    (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) i k =
      if i = 0 then (if k = 1 then 1 else 0)
      else if i = 1 then ((if k = 0 then 1 else 0) + (if k = 1 then 1 else 0))
      else (if i = k then 1 else 0) := by
  have h01 := fin_zero_ne_one' (m := m)
  rw [g0, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection, add_mul, mul_add, mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, single_mul_single_same]
  simp only [Matrix.add_apply, one_apply, single_apply]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hk0 : k = 0
    · subst hk0
      simp [h01, CharTwo.add_self_eq_zero]
    · by_cases hk1 : k = 1
      · subst hk1
        simp [h01]
      · simp [hk1, Ne.symm hk0, Ne.symm hk1]
  · by_cases hi1 : i = 1
    · subst hi1
      by_cases hk0 : k = 0
      · subst hk0
        simp [h01, Ne.symm h01]
      · by_cases hk1 : k = 1
        · subst hk1
          simp [h01, Ne.symm h01]
        · simp [hk0, hk1, Ne.symm h01, Ne.symm hk1, Ne.symm hk0]
    · simp [hi0, hi1, Ne.symm hi0, Ne.symm hi1]

theorem coe_g0_apply' (k j : Fin (m + 2)) :
    (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) k j =
      if j = 0 then (if k = 1 then 1 else 0)
      else if j = 1 then ((if k = 0 then 1 else 0) + (if k = 1 then 1 else 0))
      else (if k = j then 1 else 0) := by
  have h01 := fin_zero_ne_one' (m := m)
  rw [coe_g0_apply]
  by_cases hk0 : k = 0
  · subst hk0
    by_cases hj0 : j = 0
    · subst hj0; simp [h01]
    · by_cases hj1 : j = 1
      · subst hj1; simp [h01]
      · simp [hj0, hj1, Ne.symm hj0]
  · by_cases hk1 : k = 1
    · subst hk1
      by_cases hj0 : j = 0
      · subst hj0; simp [h01, Ne.symm h01]
      · by_cases hj1 : j = 1
        · subst hj1; simp [Ne.symm h01]
        · simp [hj0, hj1, Ne.symm h01, Ne.symm hj1]
    · by_cases hj0 : j = 0
      · subst hj0; simp [hk0, hk1]
      · by_cases hj1 : j = 1
        · subst hj1; simp [hk0, hk1]
        · simp [hk0, hk1, hj0, hj1]

theorem g0_mul_apply (s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) (i j : Fin (m + 2)) :
    ((g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * s) i j =
      if i = 0 then s 1 j else if i = 1 then s 0 j + s 1 j else s i j := by
  rw [Matrix.mul_apply]
  simp only [coe_g0_apply]
  split_ifs with h0 h1
  · simp [ite_mul]
  · simp [ite_mul, add_mul, Finset.sum_add_distrib]
  · simp [ite_mul]

theorem mul_g0_apply (s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) (i j : Fin (m + 2)) :
    (s * (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K)) i j =
      if j = 0 then s i 1 else if j = 1 then s i 0 + s i 1 else s i j := by
  rw [Matrix.mul_apply]
  simp only [coe_g0_apply']
  split_ifs with h0 h1
  · simp [mul_ite]
  · simp [mul_ite, mul_add, Finset.sum_add_distrib]
  · simp [mul_ite]

theorem g0_pow_three : g0 m K ^ 3 = 1 := by
  have h01 := fin_zero_ne_one' (m := m)
  ext i j
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, sq, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_assoc, g0_mul_apply, g0_mul_apply, g0_mul_apply, g0_mul_apply,
    Matrix.SpecialLinearGroup.coe_one]
  simp only [coe_g0_apply, one_apply]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0; simp [h01, Ne.symm h01]
    · by_cases hj1 : j = 1
      · subst hj1; simp [h01, Ne.symm h01, CharTwo.add_self_eq_zero]
      · simp [Ne.symm h01, hj0, hj1, Ne.symm hj0]
  · by_cases hi1 : i = 1
    · subst hi1
      by_cases hj0 : j = 0
      · subst hj0; simp [h01, Ne.symm h01, CharTwo.add_self_eq_zero]
      · by_cases hj1 : j = 1
        · subst hj1; simp [Ne.symm h01, CharTwo.add_self_eq_zero]
        · simp [Ne.symm h01, hj0, hj1, Ne.symm hj1]
    · simp [hi0, hi1]

theorem g0_ne_one : g0 m K ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin (m + 2)) K =>
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 0) h
  simp only [coe_g0_apply, Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h1
  simp at h1

section Centralizer

variable {s : Matrix (Fin (m + 2)) (Fin (m + 2)) K}
  (hs : s * (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) = g0 m K * s)
include hs

theorem entry_eq_zero_of_commute_g0 {j : Fin (m + 2)} (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    s 0 j = 0 ∧ s 1 j = 0 := by
  have h01 := fin_zero_ne_one' (m := m)
  have e0 := congrFun (congrFun hs 0) j
  have e1 := congrFun (congrFun hs 1) j
  rw [mul_g0_apply, g0_mul_apply] at e0 e1
  simp only [hj0, hj1, ite_false, ite_true, Ne.symm h01] at e0 e1
  have h0 : s 0 j = 0 := by
    have := e1
    rw [right_eq_add] at this
    exact this
  exact ⟨h0, by rw [← e0, h0]⟩

theorem entry_eq_zero_of_commute_g0' {i : Fin (m + 2)} (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    s i 0 = 0 ∧ s i 1 = 0 := by
  have h01 := fin_zero_ne_one' (m := m)
  have e0 := congrFun (congrFun hs i) 0
  have e1 := congrFun (congrFun hs i) 1
  rw [mul_g0_apply, g0_mul_apply] at e0 e1
  simp only [hi0, hi1, ite_false, ite_true, Ne.symm h01] at e0 e1
  have h0 : s i 0 = 0 := by
    have := e1
    rw [add_eq_right] at this
    exact this
  exact ⟨h0, by rw [e0, h0]⟩

theorem entry_eq_of_commute_g0 : s 1 0 = s 0 1 ∧ s 1 1 = s 0 0 + s 0 1 := by
  have h01 := fin_zero_ne_one' (m := m)
  have e0 := congrFun (congrFun hs 0) 0
  have e1 := congrFun (congrFun hs 0) 1
  rw [mul_g0_apply, g0_mul_apply] at e0 e1
  simp only [ite_true, Ne.symm h01, ite_false] at e0 e1
  exact ⟨e0.symm, e1.symm⟩

end Centralizer

variable (m) in
@[expose] def J01 : Finset (Fin (m + 2)) := ({0, 1} : Finset (Fin (m + 2)))ᶜ

theorem mem_J01 {i : Fin (m + 2)} : i ∈ J01 m ↔ i ≠ 0 ∧ i ≠ 1 := by
  simp [J01]

theorem card_J01 : (J01 m).card = m := by
  rw [J01, Finset.card_compl, Fintype.card_fin, Finset.card_pair fin_zero_ne_one']
  omega

omit [CharP K 2] in
theorem entry_of_mem_J0 {s : SpecialLinearGroup (Fin (m + 2)) K}
    (hs : s ∈ coordBlockSL K (J01 m)) {a b : Fin (m + 2)} (h : a = 0 ∨ a = 1 ∨ b = 0 ∨ b = 1) :
    (s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) a b = if a = b then 1 else 0 := by
  apply mem_coordBlockSL_iff.mp hs
  rcases h with h | h | h | h <;> simp [mem_J01, h]

theorem coordBlockSL_le_centralizer_g0 :
    coordBlockSL K (J01 m) ≤ Subgroup.centralizer {g0 m K} := by
  have h01 := fin_zero_ne_one' (m := m)
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply,
    mul_g0_apply]
  have hv := fun a b h => entry_of_mem_J0 (K := K) hs (a := a) (b := b) h
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      simp only [ite_true]
      rw [hv 0 1 (by simp), hv 1 0 (by simp)]
      simp [h01, Ne.symm h01]
    · by_cases hj1 : j = 1
      · subst hj1
        simp only [ite_true, Ne.symm h01, ite_false]
        rw [hv 0 0 (by simp), hv 0 1 (by simp), hv 1 1 (by simp)]
        simp [h01]
      · simp only [hj0, hj1, ite_false, ite_true]
        rw [hv 0 j (by simp), hv 1 j (by simp)]
        simp [Ne.symm hj0, Ne.symm hj1]
  · by_cases hi1 : i = 1
    · subst hi1
      by_cases hj0 : j = 0
      · subst hj0
        simp only [ite_true, Ne.symm h01, ite_false]
        rw [hv 1 1 (by simp), hv 0 0 (by simp), hv 1 0 (by simp)]
        simp [Ne.symm h01]
      · by_cases hj1 : j = 1
        · subst hj1
          simp only [ite_true, Ne.symm h01, ite_false]
          rw [hv 1 0 (by simp), hv 1 1 (by simp), hv 0 1 (by simp)]
          simp [h01, Ne.symm h01]
        · simp only [hj0, hj1, ite_false, Ne.symm h01, ite_true]
          rw [hv 0 j (by simp), hv 1 j (by simp)]
          simp [Ne.symm hj0, Ne.symm hj1]
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [hi0, hi1, ite_false, ite_true]
        rw [hv i 1 (by simp), hv i 0 (by simp)]
        simp [hi0, hi1]
      · by_cases hj1 : j = 1
        · subst hj1
          simp only [hi0, hi1, ite_false, Ne.symm h01, ite_true]
          rw [hv i 0 (by simp), hv i 1 (by simp)]
          simp [hi0, hi1]
        · simp only [hi0, hi1, hj0, hj1, ite_false]

theorem compIndicator_commute_of_mem {c : SpecialLinearGroup (Fin (m + 2)) K}
    (hc : c ∈ Subgroup.centralizer {g0 m K}) :
    compIndicator K (J01 m) * (c : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
      (c : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * compIndicator K (J01 m) := by
  have hs : (c : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
      (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
      (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * c := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hc]
  ext i j
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hi : i ∈ J01 m <;> by_cases hj : j ∈ J01 m
  · simp [hi, hj]
  · rw [ite_eq_left hi, ite_eq_right hj]
    rw [mem_J01] at hi hj
    have hj' : j = 0 ∨ j = 1 := by tauto
    rcases hj' with rfl | rfl
    · exact (entry_eq_zero_of_commute_g0' hs hi.1 hi.2).1.symm
    · exact (entry_eq_zero_of_commute_g0' hs hi.1 hi.2).2.symm
  · rw [ite_eq_right hi, ite_eq_left hj]
    rw [mem_J01] at hi hj
    have hi' : i = 0 ∨ i = 1 := by tauto
    rcases hi' with rfl | rfl
    · exact (entry_eq_zero_of_commute_g0 hs hj.1 hj.2).1
    · exact (entry_eq_zero_of_commute_g0 hs hj.1 hj.2).2
  · simp [hi, hj]

theorem conj_mem_J0_of_mem {c : SpecialLinearGroup (Fin (m + 2)) K}
    (hc : c ∈ Subgroup.centralizer {g0 m K}) {j : SpecialLinearGroup (Fin (m + 2)) K}
    (hj : j ∈ coordBlockSL K (J01 m)) : c * j * c⁻¹ ∈ coordBlockSL K (J01 m) :=
  conj_mem_coordBlockSL (compIndicator_commute_of_mem hc) hj

theorem mem_J0_of_commute_g0 {s : SpecialLinearGroup (Fin (m + 2)) K}
    (hs : (s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *
      (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
      (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * s)
    (h00 : (s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 0 = 1)
    (h01 : (s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 1 = 0) :
    s ∈ coordBlockSL K (J01 m) := by
  have hne := fin_zero_ne_one' (m := m)
  obtain ⟨h10, h11⟩ := entry_eq_of_commute_g0 hs
  rw [mem_coordBlockSL_iff]
  intro i j hij
  simp only [mem_J01, not_and_or, not_not] at hij
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0; simp [h00]
    · by_cases hj1 : j = 1
      · subst hj1; simp [h01, hne]
      · rw [(entry_eq_zero_of_commute_g0 hs hj0 hj1).1, ite_eq_right (Ne.symm hj0)]
  · by_cases hi1 : i = 1
    · subst hi1
      by_cases hj0 : j = 0
      · subst hj0; simp [h10, h01, Ne.symm hne]
      · by_cases hj1 : j = 1
        · subst hj1; simp [h11, h00, h01]
        · rw [(entry_eq_zero_of_commute_g0 hs hj0 hj1).2, ite_eq_right (Ne.symm hj1)]
    · have hj : j = 0 ∨ j = 1 := by tauto
      rcases hj with rfl | rfl
      · rw [(entry_eq_zero_of_commute_g0' hs hi0 hi1).1, ite_eq_right hi0]
      · rw [(entry_eq_zero_of_commute_g0' hs hi0 hi1).2, ite_eq_right hi1]

omit [CharP K 2] in
theorem eq_zero_or_eq_one_of_card [Finite K] (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  have h2 : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (sub_eq_zero.mp h3)

theorem exists_pow_mul_mem_J0 [Finite K] (hK : Nat.card K = 2)
    {s : SpecialLinearGroup (Fin (m + 2)) K} (hsC : s ∈ Subgroup.centralizer {g0 m K}) :
    ∃ k : ℕ, k < 3 ∧ g0 m K ^ k * s ∈ coordBlockSL K (J01 m) := by
  have hne := fin_zero_ne_one' (m := m)
  have hcomm : ∀ t ∈ Subgroup.centralizer {g0 m K},
      (t : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
        (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * t := fun t ht => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.mem_centralizer_singleton_iff.mp ht]
  have hg0C : g0 m K ∈ Subgroup.centralizer {g0 m K} :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hs := hcomm s hsC
  obtain ⟨h10, h11⟩ := entry_eq_of_commute_g0 hs
  rcases eq_zero_or_eq_one_of_card hK ((s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 0) with
    ha0 | ha1 <;>
    rcases eq_zero_or_eq_one_of_card hK ((s : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 1) with
      hb0 | hb1
  · exfalso
    have hdet := s.2
    rw [Matrix.det_eq_zero_of_column_eq_zero 0] at hdet
    · exact zero_ne_one hdet
    · intro i
      by_cases hi0 : i = 0
      · rw [hi0, ha0]
      · by_cases hi1 : i = 1
        · rw [hi1, h10, hb0]
        · exact (entry_eq_zero_of_commute_g0' hs hi0 hi1).1
  · refine ⟨2, by norm_num, mem_J0_of_commute_g0 (hcomm _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ hg0C 2) hsC)) ?_ ?_⟩
    · rw [sq, mul_assoc, Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply,
        Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply]
      simp only [ite_true, Ne.symm hne, ite_false]
      rw [h10, ha0, hb1, zero_add]
    · rw [sq, mul_assoc, Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply,
        Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply]
      simp only [ite_true, Ne.symm hne, ite_false]
      rw [h11, ha0, hb1, zero_add, CharTwo.add_self_eq_zero]
  · refine ⟨0, by norm_num, ?_⟩
    rw [pow_zero, one_mul]
    exact mem_J0_of_commute_g0 hs ha1 hb0
  · refine ⟨1, by norm_num, mem_J0_of_commute_g0 (hcomm _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ hg0C 1) hsC)) ?_ ?_⟩
    · rw [pow_one, Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply]
      simp only [ite_true]
      rw [h10, hb1]
    · rw [pow_one, Matrix.SpecialLinearGroup.coe_mul, g0_mul_apply]
      simp only [ite_true]
      rw [h11, ha1, hb1, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem commutatorElement_mul_of_commute {G : Type*} [Group G] {u v a b : G} (hua : Commute u a)
    (hub : Commute u b) (hva : Commute v a) (hvb : Commute v b) (huv : Commute u v) :
    ⁅u * a, v * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : Commute u (a * (v * b) * a⁻¹ * b⁻¹) :=
    (((hua.mul_right (huv.mul_right hub)).mul_right hua.inv_right).mul_right hub.inv_right)
  have h2 : Commute v (a * b * a⁻¹ * b⁻¹) :=
    ((hva.mul_right hvb).mul_right hva.inv_right).mul_right hvb.inv_right
  have h3 : a * (v * b) * a⁻¹ * b⁻¹ = v * (a * b * a⁻¹ * b⁻¹) := by
    rw [← mul_assoc a v b, ← hva.eq]
    group
  calc u * a * (v * b) * (u * a)⁻¹ * (v * b)⁻¹
      = u * (a * (v * b) * a⁻¹) * (u⁻¹ * b⁻¹) * v⁻¹ := by group
    _ = u * (a * (v * b) * a⁻¹) * (b⁻¹ * u⁻¹) * v⁻¹ := by rw [hub.inv_inv.eq]
    _ = (u * (a * (v * b) * a⁻¹ * b⁻¹)) * u⁻¹ * v⁻¹ := by group
    _ = (a * (v * b) * a⁻¹ * b⁻¹) * u * u⁻¹ * v⁻¹ := by rw [h1.eq]
    _ = v * (a * b * a⁻¹ * b⁻¹) * v⁻¹ := by rw [h3]; group
    _ = (a * b * a⁻¹ * b⁻¹) * v * v⁻¹ := by rw [h2.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_centralizer_g0_le [Finite K] (hK : Nat.card K = 2) :
    ⁅Subgroup.centralizer {g0 m K}, Subgroup.centralizer {g0 m K}⁆ ≤ coordBlockSL K (J01 m) := by
  rw [Subgroup.commutator_le]
  intro c₁ hc₁ c₂ hc₂
  have hcg : ∀ c ∈ Subgroup.centralizer {g0 m K}, ∀ k : ℕ, Commute (g0 m K ^ k)⁻¹ c :=
    fun c hc k => ((Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
      k).inv_left)
  obtain ⟨k₁, -, hj₁⟩ := exists_pow_mul_mem_J0 hK hc₁
  obtain ⟨k₂, -, hj₂⟩ := exists_pow_mul_mem_J0 hK hc₂
  have hC := coordBlockSL_le_centralizer_g0 (m := m) (K := K)
  have e₁ : c₁ = (g0 m K ^ k₁)⁻¹ * (g0 m K ^ k₁ * c₁) := by group
  have e₂ : c₂ = (g0 m K ^ k₂)⁻¹ * (g0 m K ^ k₂ * c₂) := by group
  rw [e₁, e₂, commutatorElement_mul_of_commute (hcg _ (hC hj₁) k₁) (hcg _ (hC hj₂) k₁)
    (hcg _ (hC hj₁) k₂) (hcg _ (hC hj₂) k₂) ((Commute.pow_pow_self (g0 m K) k₁ k₂).inv_inv)]
  exact (coordBlockSL K (J01 m)).mul_mem ((coordBlockSL K (J01 m)).mul_mem
    ((coordBlockSL K (J01 m)).mul_mem hj₁ hj₂) ((coordBlockSL K (J01 m)).inv_mem hj₁))
    ((coordBlockSL K (J01 m)).inv_mem hj₂)

omit [CharP K 2] in
theorem isQuasisimple_J0 (hm : 3 ≤ m) : CFSG.IsQuasisimple (coordBlockSL K (J01 m)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MonoidHom.ofInjective (blockSLOn_injective (k := K) (J01 m))).trans
      (MulEquiv.subgroupCongr (range_blockSLOn (J01 m))))
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by rw [card_J01]; exact hm))

theorem layer_centralizer_g0 [Finite K] (hK : Nat.card K = 2) (hm : 3 ≤ m) {L' : Type}
    [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin (m + 2)) K →* L'}
    (hinj : ∀ j ∈ coordBlockSL K (J01 m), φ j = 1 → j = 1) :
    CFSG.Assembly.LargeEvenLayer ((Subgroup.centralizer {g0 m K}).map φ) =
        (coordBlockSL K (J01 m)).map φ ∧
      CFSG.Assembly.IsComponentOf ((coordBlockSL K (J01 m)).map φ)
        ((Subgroup.centralizer {g0 m K}).map φ) :=
  CFSG.StandardType.TypeA.layer_eq_of_block coordBlockSL_le_centralizer_g0
    (fun _ hc _ hj => conj_mem_J0_of_mem hc hj) (commutator_centralizer_g0_le hK) hinj
    (isQuasisimple_J0 hm)

omit [CharP K 2] in
theorem col_eq_of_commute_J0 [Finite K] (hK : Nat.card K = 2) (hm : 2 ≤ m)
    {h : SpecialLinearGroup (Fin (m + 2)) K}
    (hh : ∀ s ∈ coordBlockSL K (J01 m), s * h = h * s) :
    ∀ j ∈ J01 m, ∀ i,
      (h : Matrix (Fin (m + 2)) (Fin (m + 2)) K) i j = if i = j then 1 else 0 := by
  intro j hj
  obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_ne (by rw [card_J01]; omega : 1 < (J01 m).card) j
  have hjk : j ≠ k := Ne.symm hkj
  have hT : SpecialLinearGroup.transvection hjk (1 : K) ∈ coordBlockSL K (J01 m) := by
    rw [mem_coordBlockSL_iff]
    intro a b hab
    rw [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, one_apply, single_apply]
    have : ¬ (j = a ∧ k = b) := by
      rintro ⟨rfl, rfl⟩
      rcases hab with h | h <;> contradiction
    simp [this]
  have hc := congrArg (fun g : SpecialLinearGroup (Fin (m + 2)) K =>
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K)) (hh _ hT)
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection, add_mul,
    mul_add, Matrix.one_mul, Matrix.mul_one] at hc
  have hcol : ∀ a, (h : Matrix (Fin (m + 2)) (Fin (m + 2)) K) a j =
      if a = j then (h : Matrix (Fin (m + 2)) (Fin (m + 2)) K) k k else 0 := by
    intro a
    have e := congrFun (congrFun hc a) k
    rw [Matrix.add_apply, Matrix.add_apply, mul_single_apply_same, mul_one, add_right_inj] at e
    by_cases haj : a = j
    · subst haj
      rw [single_mul_apply_same, one_mul] at e
      rw [ite_eq_left rfl, e]
    · rw [single_mul_apply_of_ne _ _ _ _ _ haj] at e
      rw [ite_eq_right haj, e]
  have hkk : (h : Matrix (Fin (m + 2)) (Fin (m + 2)) K) k k = 1 := by
    rcases eq_zero_or_eq_one_of_card hK ((h : Matrix (Fin (m + 2)) (Fin (m + 2)) K) k k) with
      h0 | h1
    · exfalso
      have hdet := h.2
      rw [Matrix.det_eq_zero_of_column_eq_zero j (fun a => by rw [hcol a, h0, ite_self])] at hdet
      exact zero_ne_one hdet
    · exact h1
  intro i
  rw [hcol i, hkk]

theorem g0_mulVec_apply (w : Fin (m + 2) → K) :
    ((g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w) 0 = w 1 ∧
      ((g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w) 1 = w 0 + w 1 := by
  have hne := fin_zero_ne_one' (m := m)
  simp only [Matrix.mulVec, dotProduct, coe_g0_apply, ite_true, Ne.symm hne, ite_false, ite_mul,
    one_mul, zero_mul, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  exact ⟨trivial, trivial⟩

theorem fixes_of_col_eq {h : Matrix (Fin (m + 2)) (Fin (m + 2)) K}
    (hcol : ∀ j ∈ J01 m, ∀ i, h i j = if i = j then 1 else 0) {w : Fin (m + 2) → K}
    (hw : (g0 m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ w = w) : h *ᵥ w = w := by
  obtain ⟨e0, e1⟩ := g0_mulVec_apply (K := K) w
  rw [hw] at e0 e1
  have hw0 : w 0 = 0 := by
    have := e1
    rw [right_eq_add] at this
    exact this
  have hw1 : w 1 = 0 := by rw [← e0, hw0]
  ext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (g := fun j => (if i = j then 1 else 0) * w j)]
  · simp
  · intro j _
    by_cases hj : j ∈ J01 m
    · rw [hcol j hj i]
    · rw [mem_J01] at hj
      have hj' : j = 0 ∨ j = 1 := by tauto
      rcases hj' with rfl | rfl
      · rw [hw0, mul_zero, mul_zero]
      · rw [hw1, mul_zero, mul_zero]

end CFSG.StandardType.TwoThree
