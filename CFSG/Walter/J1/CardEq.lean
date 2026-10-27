module

public import CFSG.Walter.J1.Weights
public import CFSG.Walter.J1.Arith
public import CFSG.Walter.J1.CountSeven
public import CFSG.Walter.J1.SevenIndex

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

omit [Finite G] in
theorem sum_ite_eq [Fintype G] (H : Subgroup G) (k c : ℕ)
    [DecidablePred (fun u : G => orderOf u = 2 ∧ u ∉ H)] :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H),
      (if cosetInvolutions H (rightCoset H u) = k then c else 0) =
      c * (involutionsOf H k).ncard := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [Finset.filter_filter, Set.ncard_eq_toFinset_card']
  congr 1
  ext u
  rw [Set.mem_toFinset]
  simp [involutionsOf, mem_involutions, and_assoc]

omit [Finite G] in
theorem sum_ite_benderC [Fintype G] (H : Subgroup G)
    [DecidablePred (fun u : G => orderOf u = 2 ∧ u ∉ H)]
    [∀ u : G, Decidable (cosetInvolutions H (rightCoset H u) = 1 ∧
      (∃ g ∈ H, g ≠ 1 ∧ g * u = u * g))] :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H),
      (if cosetInvolutions H (rightCoset H u) = 1 ∧ (∃ g ∈ H, g ≠ 1 ∧ g * u = u * g) then 2
        else 0) = 2 * benderC H := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [Finset.filter_filter, benderC, Set.ncard_eq_toFinset_card']
  congr 1
  ext u
  rw [Set.mem_toFinset]
  simp [involutionsOf, mem_involutions, and_assoc]

omit [Finite G] in
theorem sum_ite_eq_zero [Fintype G] (H : Subgroup G) (k : ℕ) (f : G → ℕ)
    [DecidablePred (fun u : G => orderOf u = 2 ∧ u ∉ H)]
    (hk : (involutionsOf H k).ncard = 0) :
    ∑ u ∈ Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H),
      (if cosetInvolutions H (rightCoset H u) = k then f u else 0) = 0 := by
  refine Finset.sum_eq_zero fun u hu => ?_
  split_ifs with hn
  · exfalso
    rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact hk u ⟨mem_involutions.mpr hu.1, hu.2, hn⟩
  · rfl

include h in
theorem count_relations (Q : Sylow 2 G) {d : ℕ}
    (hd3 : ∀ X : Subgroup G, Nat.card X = 3 →
      {u : G | orderOf u = 2 ∧ u ∈ Subgroup.centralizer (X : Set G)}.ncard = 2 * d - 1 ∧
      {u : G | orderOf u = 2 ∧ ∀ x ∈ X, u * x * u⁻¹ = x⁻¹}.ncard = 6 * d)
    {y₀ : G} (hy₀H : y₀ ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (hy₀ : orderOf y₀ = 7) :
    ∃ b0 b1 b2 b3 b6 b7 c m : ℕ,
      {u : G | orderOf u = 2}.ncard = 7 + (b1 + 2 * b2 + 3 * b3 + 6 * b6 + 7 * b7) ∧
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index =
        1 + (b0 + b1 + b2 + b3 + b6 + b7) ∧
      b2 = 0 ∧ b6 = 28 ∧ 3 * b3 + 168 = 168 * d ∧
      7 * b7 = 8 * {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard ∧
      2 * c + 112 * (if {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard = 0 then 0 else 1)
        + 112 = 112 * d ∧
      b1 = c + 168 * m := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set H := Subgroup.normalizer ((Q : Subgroup G) : Set G) with hH
  set U := Finset.univ.filter (fun u : G => orderOf u = 2 ∧ u ∉ H)
  set Jk : ℕ → ℕ := fun k => (involutionsOf H k).ncard
  have hJk : ∀ k, Jk k = k * cosetCount H k := fun k => involutionsOf_ncard H k
  have hW : ∀ u ∈ U, _ := fun u hu => h.weights Q hH (Finset.mem_filter.mp hu).2.1
    (Finset.mem_filter.mp hu).2.2 (n := cosetInvolutions H (rightCoset H u)) rfl
  have S2 := h.sum_invOrd_two Q hH
  have S6 := h.sum_invOrd_six Q hH
  have S3 := h.sum_invOrd_three Q hH (fun X hX => (hd3 X hX).2)
  have S7 := h.sum_invOrd_seven Q hH hy₀H hy₀
  have Sk := h.sum_kap Q hH (fun X hX => (hd3 X hX).1)
  have Sk7 := h.sum_kap_mul_invOrd_seven Q hH hy₀H hy₀
  rw [Finset.sum_congr rfl (fun u hu => (hW u hu).2.1), Finset.sum_add_distrib, sum_ite_eq,
    sum_ite_eq] at S2
  rw [Finset.sum_congr rfl (fun u hu => (hW u hu).2.2.1), sum_ite_eq] at S6
  rw [Finset.sum_congr rfl (fun u hu => (hW u hu).2.2.2.1), Finset.sum_add_distrib, sum_ite_eq,
    sum_ite_eq] at S3
  rw [Finset.sum_congr rfl (fun u hu => (hW u hu).2.2.2.2.1), sum_ite_eq] at S7
  have hJ2 : Jk 2 = 0 := by simp only [Jk]; omega
  have hJ6 : Jk 6 = 168 := by simp only [Jk]; omega
  have hkap : ∀ u ∈ U, kap H u =
      (if cosetInvolutions H (rightCoset H u) = 1 ∧ (∃ g ∈ H, g ≠ 1 ∧ g * u = u * g) then 2
        else 0) + (if cosetInvolutions H (rightCoset H u) = 2 then kap H u else 0) +
        (if cosetInvolutions H (rightCoset H u) = 7 then kap H u else 0) := by
    intro u hu
    obtain ⟨h0, -, -, -, -, h1, h36⟩ := hW u hu
    rcases h0 with h0 | h0 | h0 | h0 | h0 <;> rw [h0]
    · obtain ⟨hk, hk2⟩ := h1 h0
      by_cases hC : ∃ g ∈ H, g ≠ 1 ∧ g * u = u * g
      · simp [hC, hk2.mpr hC]
      · simp only [hC, and_false, ite_false]
        rcases hk with hk | hk
        · simp [hk]
        · exact absurd (hk2.mp hk) hC
    · simp
    · simp [h36 (Or.inl h0)]
    · simp [h36 (Or.inr h0)]
    · simp
  rw [Finset.sum_congr rfl hkap, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_ite_benderC, sum_ite_eq_zero H 2 _ hJ2, add_zero] at Sk
  have hk7 : ∀ u ∈ U, kap H u * invOrd H u 7 =
      6 * (if cosetInvolutions H (rightCoset H u) = 7 then kap H u else 0) := by
    intro u hu
    rw [(hW u hu).2.2.2.2.1]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hk7, ← Finset.mul_sum] at Sk7
  have hJ : {u : G | orderOf u = 2}.ncard = 7 + (Jk 1 + Jk 2 + Jk 3 + Jk 6 + Jk 7) := by
    have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard {u : G | orderOf u = 2} (H : Set G)
    have h2 : ({u : G | orderOf u = 2} ∩ (H : Set G)).ncard = 7 := by
      rw [← h.ncard_involutions_normalizer Q]
      congr 1
    have h3 : ({u : G | orderOf u = 2} \ (H : Set G)).ncard = U.card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext u
      rw [Set.mem_toFinset]
      simp [U]
    have h4 : U.card = Jk 1 + Jk 2 + Jk 3 + Jk 6 + Jk 7 := by
      have : ∀ u ∈ U, (1 : ℕ) = (if cosetInvolutions H (rightCoset H u) = 1 then 1 else 0) +
          (if cosetInvolutions H (rightCoset H u) = 2 then 1 else 0) +
          (if cosetInvolutions H (rightCoset H u) = 3 then 1 else 0) +
          (if cosetInvolutions H (rightCoset H u) = 6 then 1 else 0) +
          (if cosetInvolutions H (rightCoset H u) = 7 then 1 else 0) := by
        intro u hu
        rcases (hW u hu).1 with h0 | h0 | h0 | h0 | h0 <;> simp [h0]
      rw [Finset.card_eq_sum_ones, Finset.sum_congr rfl this, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_eq,
        sum_ite_eq, sum_ite_eq, sum_ite_eq, sum_ite_eq]
      simp only [Jk, one_mul]
    rw [← h1, h2, h3, h4]
  have hcard : 168 ≤ Nat.card G := by
    rw [← h.card_normalizer_sylow'' Q]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hI : H.index = 1 + (cosetCount H 0 + cosetCount H 1 + cosetCount H 2 + cosetCount H 3 +
      cosetCount H 6 + cosetCount H 7) := by
    rw [index_eq]
    congr 1
    have hsub : ({0, 1, 2, 3, 6, 7} : Finset ℕ) ⊆ Finset.range (Nat.card G + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]
      omega
    rw [← Finset.sum_subset hsub]
    · simp [Finset.sum_insert]
      ring
    · intro k _ hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have h0 : Jk k = 0 := by
        simp only [Jk]
        rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
        rintro u ⟨hu, huH, hnu⟩
        have := (hW u (by simp [U, mem_involutions.mp hu, huH])).1
        rw [hnu] at this
        omega
      rw [hJk] at h0
      rcases Nat.mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 hk.1
      · exact h0
  obtain ⟨m, hm⟩ := exists_cosetCount_one_eq H
  rw [h.card_normalizer_sylow'' Q] at hm
  refine ⟨cosetCount H 0, cosetCount H 1, cosetCount H 2, cosetCount H 3, cosetCount H 6,
    cosetCount H 7, benderC H, m, ?_, hI, ?_, ?_, ?_, ?_, ?_, by rw [hm]; ring⟩
  · rw [hJ]
    simp only [hJk]
    ring
  · have := hJk 2
    omega
  · have := hJk 6
    omega
  · have := hJk 3
    have := hJk 6
    simp only [Jk] at *
    omega
  · have := hJk 7
    simp only [Jk] at *
    omega
  · simp only [Jk] at *
    omega

include h in
theorem card_eq : Nat.card G = 175560 := by
  classical
  have hs := h.isSimpleGroup
  obtain ⟨Q, -⟩ := h.exists_sylow_mem_t
  obtain ⟨d, hd13, hd3, hd5⟩ := h.exists_d
  obtain ⟨y₀, hy₀H, hy₀⟩ : ∃ y₀ ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G),
      orderOf y₀ = 7 := by
    have h48 := h.ncard_orderOf_seven Q
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h48]; norm_num)
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨b0, b1, b2, b3, b6, b7, c, m, hJ, hI, hb2, hb6, hb3, hb7, hc, hm⟩ :=
    h.count_relations Q hd3 hy₀H hy₀
  have hG120 : {u : G | orderOf u = 2}.ncard * 120 = Nat.card G := h.ncard_involutions_mul
  have hG168 : 168 * (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index = Nat.card G := by
    rw [← h.card_normalizer_sylow'' Q]
    exact Subgroup.card_mul_index _
  obtain ⟨P, hP⟩ := h.exists_card_odd (Or.inr rfl)
  have h5 : {u : G | orderOf u = 2}.ncard % 5 = d % 5 := by
    rw [ncard_involutions_mod_five hP, hd5 P hP]
  set r := {u : G | orderOf u = 2 ∧ u * y₀ * u⁻¹ = y₀⁻¹}.ncard with hr
  set J := {u : G | orderOf u = 2}.ncard with hJdef
  set I := (Subgroup.normalizer ((Q : Subgroup G) : Set G)).index with hIdef
  subst hb2 hb6
  have hGJ : 120 * J = 168 * I := by clear * - hG120 hG168; omega
  have h89 : Nat.card G ≠ 74760 := fun h0 => false_of_card_sylow (p := 89) (M := 840)
    (hp := ⟨by norm_num⟩) (by rw [h0]) (by norm_num) (by norm_num) divisors_840_89
  by_cases hr0 : r = 0
  ·
    simp only [hr0, ↓reduceIte] at hc
    have hb7' : b7 = 0 := by clear * - hb7 hr0; omega
    subst hb7'
    rcases arith_e0 hd13 (J := J) (I := I) (b0 := b0) (b3 := b3) (c := c) (m := m)
      (by clear * - hJ hm; omega) (by clear * - hI hm; omega) hb3 (by clear * - hc; omega) hGJ
      h5 with hJ1 | hJ1
    · exact (false_of_card_sylow (p := 73) (M := 840) (hp := ⟨by norm_num⟩)
        (by rw [← hG120, hJ1]) (by norm_num) (by norm_num) divisors_840_73).elim
    · exact absurd (by rw [← hG120, hJ1]) h89
  · simp only [hr0, ↓reduceIte] at hc
    have hd3' : d = 3 := by clear * - hc hd13; omega
    subst hd3'
    obtain ⟨hJr, hb0r⟩ := arith_e1 (J := J) (I := I) (b0 := b0) (b3 := b3) (b7 := b7) (c := c)
      (m := m) (r := r) (by clear * - hJ hm; omega) (by clear * - hI hm; omega) hb3 hb7
      (by clear * - hc; omega) hGJ
    obtain ⟨t', ht', ht'y⟩ : ∃ t', orderOf t' = 2 ∧ t' * y₀ * t'⁻¹ = y₀⁻¹ := by
      obtain ⟨t', ht'⟩ := Set.nonempty_of_ncard_ne_zero hr0
      exact ⟨t', ht'.1, ht'.2⟩
    have hy₀1 : y₀ ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hy₀; omega
    have hy₀c : Nat.Coprime (orderOf y₀) 30 := by rw [hy₀]; norm_num
    have hrA : r = Nat.card (Subgroup.centralizer ({y₀} : Set G)) :=
      h.ncard_inverting_eq hy₀1 hy₀c ht' ht'y
    by_cases hr7 : r = 7
    · rw [hr7] at hJr hb0r
      rcases arith_r7 hJr hb0r (by clear * - h5; omega) with hJ1 | hJ1
      · exact absurd (by rw [← hG120, hJ1]) h89
      · rw [← hG120, hJ1]
    ·
      exfalso
      set A := Subgroup.centralizer ({y₀} : Set G)
      set N := Subgroup.normalizer ((A : Subgroup G) : Set G)
      set L := N ⊓ Subgroup.centralizer ({t'} : Set G)
      have hNA : Nat.card N = Nat.card A * Nat.card L := h.card_normalizer_eq hy₀1 hy₀c ht' ht'y
      have hidx : Nat.card A ∣ N.index - 1 := h.dvd_index_sub_one hy₀1 hy₀c ht' ht'y
      have ht'N : t' ∈ N := mem_normalizer_of_conj_mem fun a ha => by
        rw [h.inv_of_mem_centralizer hy₀1 hy₀c ht' ht'y a ha]
        exact A.inv_mem ha
      have hL120 : Nat.card L ∣ 120 := by
        rw [← h.card_centralizer_involution ht']
        exact Subgroup.card_dvd_of_le inf_le_right
      have hL2 : 2 ∣ Nat.card L := by
        rw [← ht']
        exact Subgroup.orderOf_dvd_natCard L ⟨ht'N, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have hGN := N.card_mul_index
      have h7A : 7 ∣ Nat.card A := by
        rw [← hy₀]
        exact Subgroup.orderOf_dvd_natCard A (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      have hcop := h.coprime_card_centralizer hy₀1 hy₀c
      rw [← hrA] at hNA hidx h7A hcop
      exact arith_index (a := r) (k := Nat.card L) (I := N.index) h7A hr7 hcop hJr hb0r
        (by rw [← hNA, hGN, ← hG120]; ring) hidx hL120 hL2

end JankoHyp

end CFSG.Walter.J1
