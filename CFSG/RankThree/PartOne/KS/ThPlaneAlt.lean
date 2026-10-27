module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.RankThree.PartOne.ThPlane

open Equiv Equiv.Perm Subgroup

theorem cycleType_eq_of_orderOf {σ : Perm (Fin 9)} {n : ℕ} (hn : n.Prime) (hn2 : 5 ≤ n)
    (h : orderOf σ = n) : σ.cycleType = {n} := by
  have hlcm : σ.cycleType.lcm = n := by rw [Perm.lcm_cycleType, h]
  have hmem : ∀ m ∈ σ.cycleType, m = n := by
    intro m hm
    have h1 : m ∣ n := hlcm ▸ Multiset.dvd_lcm hm
    have h2 : 2 ≤ m := Perm.two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime hn).mp h1 with h3 | h3
    · omega
    · exact h3
  have hne : σ.cycleType ≠ 0 := by
    intro h0
    have : σ = 1 := Perm.cycleType_eq_zero.mp h0
    rw [this, orderOf_one] at h
    omega
  have hsum : σ.cycleType.sum ≤ 9 := by
    rw [Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) n :=
    Multiset.eq_replicate_of_mem hmem
  have hsum' : Multiset.card σ.cycleType * n ≤ 9 := by
    have := hsum
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at this
    exact this
  have hcard1 : Multiset.card σ.cycleType = 1 := by
    have hpos : 0 < Multiset.card σ.cycleType := Multiset.card_pos.mpr hne
    by_contra hc
    have h2 : 2 ≤ Multiset.card σ.cycleType := by omega
    have := Nat.mul_le_mul h2 hn2
    omega
  rw [hrep, hcard1]
  rfl

theorem card_centralizer_cycle {σ : Perm (Fin 9)} {n : ℕ} (hσ : σ.cycleType = {n}) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 9)))) = (9 - n).factorial * n := by
  rw [Perm.nat_card_centralizer, hσ]
  simp

theorem exists_two_fixed {σ : Perm (Fin 9)} {n : ℕ} (hσ : σ.cycleType = {n}) (hn : n ≤ 7) :
    ∃ i j : Fin 9, i ≠ j ∧ σ i = i ∧ σ j = j := by
  have h := Perm.card_fixedPoints σ
  rw [hσ] at h
  simp only [Multiset.sum_singleton, Fintype.card_fin] at h
  have h2 : 1 < Fintype.card (Function.fixedPoints σ) := by omega
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij⟩ := Fintype.one_lt_card_iff_nontrivial.mp h2 |>.exists_pair_ne
  exact ⟨i, j, fun h => hij (Subtype.ext h), hi, hj⟩

theorem card_centralizer_alt {σ : Perm (Fin 9)} {n : ℕ} (hσ : σ.cycleType = {n}) (hn : n ≤ 7) :
    2 * Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) :
      Subgroup (Perm (Fin 9))) = (9 - n).factorial * n := by
  set C : Subgroup (Perm (Fin 9)) := Subgroup.centralizer ({σ} : Set (Perm (Fin 9))) with hC
  let f : C →* ℤˣ := Perm.sign.comp C.subtype
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_fixed hσ hn
  have hτ : swap i j ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have := Equiv.mul_swap_eq_swap_mul σ i j
    rw [hi, hj] at this
    exact this.symm
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨swap i j, hτ⟩, by simp [f, Perm.sign_swap hij]⟩
  have hrange : Nat.card f.range = 2 := by
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, Nat.card_eq_fintype_card]
    simp
  have hker : f.ker = (alternatingGroup (Fin 9)).subgroupOf C := rfl
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hker] at h1
  have h2 : Nat.card ((alternatingGroup (Fin 9)).subgroupOf C) =
      Nat.card (C ⊓ alternatingGroup (Fin 9) : Subgroup (Perm (Fin 9))) := by
    have hmap : ((alternatingGroup (Fin 9)).subgroupOf C).map C.subtype =
        C ⊓ alternatingGroup (Fin 9) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Subgroup.mem_inf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hxC, hxA⟩
        exact ⟨⟨x, hxC⟩, hxA, rfl⟩
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  rw [h2, card_centralizer_cycle hσ] at h1
  linarith

theorem card_centralizer_alt_five {σ : Perm (Fin 9)} (hσ : σ.cycleType = {5}) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) :
      Subgroup (Perm (Fin 9))) = 60 := by
  have := card_centralizer_alt hσ (by norm_num)
  have h : (9 - 5).factorial * 5 = 120 := by decide
  rw [h] at this
  omega

theorem card_centralizer_alt_seven {σ : Perm (Fin 9)} (hσ : σ.cycleType = {7}) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) :
      Subgroup (Perm (Fin 9))) = 7 := by
  have := card_centralizer_alt hσ (by norm_num)
  have h : (9 - 7).factorial * 7 = 14 := by decide
  rw [h] at this
  omega

theorem map_le_centralizer_alt (g : alternatingGroup (Fin 9))
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : ∀ h ∈ H, Commute h g) :
    H.map (alternatingGroup (Fin 9)).subtype ≤ Subgroup.centralizer ({(g : Perm (Fin 9))} :
      Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) := by
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨?_, h.2⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hH h hh).eq)

theorem card_dvd_four_of_commute_five (g : alternatingGroup (Fin 9)) (hg : orderOf g = 5)
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : ∀ h ∈ H, Commute h g) (h2 : IsPGroup 2 H) :
    Nat.card H ∣ 4 := by
  have hord : orderOf (g : Perm (Fin 9)) = 5 := by
    rw [← hg]; exact (Subgroup.orderOf_coe g)
  have hct := cycleType_eq_of_orderOf (n := 5) Nat.prime_five le_rfl hord
  have hdvd : Nat.card H ∣ Nat.card (Subgroup.centralizer ({(g : Perm (Fin 9))} :
      Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) : Subgroup (Perm (Fin 9))) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (alternatingGroup (Fin 9)))]
    exact Subgroup.card_dvd_of_le (map_le_centralizer_alt g H hH)
  rw [card_centralizer_alt_five hct] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ k) 15 := Nat.Coprime.pow_left k (by norm_num)
  have : 2 ^ k ∣ 4 * 15 := by simpa using hdvd
  exact hcop.dvd_of_dvd_mul_right this

theorem eq_bot_of_commute_seven (g : alternatingGroup (Fin 9)) (hg : orderOf g = 7)
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : ∀ h ∈ H, Commute h g) (h2 : IsPGroup 2 H) :
    H = ⊥ := by
  have hord : orderOf (g : Perm (Fin 9)) = 7 := by
    rw [← hg]; exact (Subgroup.orderOf_coe g)
  have hct := cycleType_eq_of_orderOf (n := 7) (by decide) (by norm_num) hord
  have hdvd : Nat.card H ∣ Nat.card (Subgroup.centralizer ({(g : Perm (Fin 9))} :
      Set (Perm (Fin 9))) ⊓ alternatingGroup (Fin 9) : Subgroup (Perm (Fin 9))) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (alternatingGroup (Fin 9)))]
    exact Subgroup.card_dvd_of_le (map_le_centralizer_alt g H hH)
  rw [card_centralizer_alt_seven hct] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [hk] at hdvd
  have hcop : Nat.Coprime (2 ^ k) 7 := Nat.Coprime.pow_left k (by norm_num)
  have h1 : 2 ^ k = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  exact Subgroup.eq_bot_of_card_eq H (hk.trans h1)

theorem exists_conj_alt {n : ℕ} (hn : n.Prime) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (g g' : alternatingGroup (Fin 9)) (hg : orderOf g = n) (hg' : orderOf g' = n) :
    ∃ h : alternatingGroup (Fin 9), h * g * h⁻¹ = g' := by
  have hct : (g : Perm (Fin 9)).cycleType = {n} :=
    cycleType_eq_of_orderOf hn hn5 (by rw [← hg]; exact (Subgroup.orderOf_coe g))
  have hct' : (g' : Perm (Fin 9)).cycleType = {n} :=
    cycleType_eq_of_orderOf hn hn5 (by rw [← hg']; exact (Subgroup.orderOf_coe g'))
  have hconj : IsConj (g : Perm (Fin 9)) (g' : Perm (Fin 9)) :=
    Perm.isConj_iff_cycleType_eq.mpr (hct.trans hct'.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_fixed hct hn7
  have hcomm : (g : Perm (Fin 9)) * swap i j = swap i j * g := by
    have := Equiv.mul_swap_eq_swap_mul (g : Perm (Fin 9)) i j
    rw [hi, hj] at this
    exact this
  by_cases hs : Perm.sign c = 1
  · exact ⟨⟨c, hs⟩, Subtype.ext hc⟩
  · have hs' : Perm.sign c = -1 := (Int.units_eq_one_or _).resolve_left hs
    refine ⟨⟨c * swap i j, ?_⟩, Subtype.ext ?_⟩
    · show Perm.sign (c * swap i j) = 1
      rw [map_mul, hs', Perm.sign_swap hij]
      rfl
    · show c * swap i j * g * (c * swap i j)⁻¹ = g'
      calc c * swap i j * g * (c * swap i j)⁻¹ = c * (swap i j * g * (swap i j)⁻¹) * c⁻¹ := by
            simp [mul_assoc]
        _ = c * g * c⁻¹ := by rw [← hcomm]; simp [mul_assoc]
        _ = g' := hc

end CFSG.RankThree.PartOne.ThPlane
