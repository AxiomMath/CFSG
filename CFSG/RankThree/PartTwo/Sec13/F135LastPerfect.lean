module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem ln_closure_normal {G : Type*} [Group G] (S : Set G)
    (hS : ∀ g : G, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : (Subgroup.closure S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS g x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem ln_pow_odd_of_sq_eq_one {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1) {b : ℕ}
    (hb : Odd b) : x ^ b = x := by
  obtain ⟨m, rfl⟩ := hb
  rw [pow_succ, pow_mul, hx, one_pow, one_mul]

theorem ln_surj_of_map_top {K : Type*} [Group K] (N N₁ : Subgroup K) [N.Normal] [N₁.Normal]
    (h : N₁.map (QuotientGroup.mk' N) = ⊤) :
    Function.Surjective ((QuotientGroup.mk' N₁).comp N.subtype) := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hk : QuotientGroup.mk' N k ∈ N₁.map (QuotientGroup.mk' N) := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨n₁, hn₁, hn₁k⟩ := Subgroup.mem_map.mp hk
  have hnk : (n₁ : K ⧸ N) = (k : K ⧸ N) := hn₁k
  have hnN : n₁⁻¹ * k ∈ N := QuotientGroup.eq.mp hnk
  refine ⟨⟨n₁⁻¹ * k, hnN⟩, ?_⟩
  show ((n₁⁻¹ * k : K) : K ⧸ N₁) = (k : K ⧸ N₁)
  rw [QuotientGroup.eq]
  have hc : k⁻¹ * n₁ * k⁻¹⁻¹ ∈ N₁ := (inferInstance : N₁.Normal).conj_mem n₁ hn₁ k⁻¹
  rw [inv_inv] at hc
  have e : (n₁⁻¹ * k)⁻¹ * k = k⁻¹ * n₁ * k := by group
  rw [e]
  exact hc

theorem normal_dichotomy {K : Type*} [Group K] [Finite K] (hKperf : commutator K = ⊤)
    (N : Subgroup K) [N.Normal] (hNodd : Odd (Nat.card N)) (hS : IsSimpleGroup (K ⧸ N))
    (N₁ : Subgroup K) [N₁.Normal] : N₁ = ⊤ ∨ N₁ ≤ N := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hKperf
  haveI : (N₁.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  rcases hS.eq_bot_or_eq_top_of_normal (N₁.map (QuotientGroup.mk' N)) with h | h
  · right
    intro n hn
    have hmem : QuotientGroup.mk' N n ∈ N₁.map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hn
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff n).mp hmem
  · left
    haveI : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥N hNodd
    have hsolv : Group.IsSolvable (K ⧸ N₁) :=
      Group.isSolvable_of_surjective (ln_surj_of_map_top N N₁ h)
    have hsub : Subsingleton (K ⧸ N₁) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable (K ⧸ N₁) hsolv
    exact (Subgroup.eq_top_iff' N₁).mpr fun x => (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

theorem closure_twoElements_eq_top {K : Type*} [Group K] [Finite K] (hKperf : commutator K = ⊤)
    (N : Subgroup K) [N.Normal] (hNodd : Odd (Nat.card N)) (hS : IsSimpleGroup (K ⧸ N))
    (heven : Even (Nat.card (K ⧸ N))) :
    Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} = ⊤ := by
  have hSconj : ∀ g : K, ∀ s ∈ {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1},
      g * s * g⁻¹ ∈ {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} := by
    rintro g s ⟨n, hn⟩
    exact ⟨n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩
  haveI : (Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1}).Normal :=
    ln_closure_normal _ hSconj
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K ⧸ N) 2 (even_iff_two_dvd.mp heven)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hkk : (k : K ⧸ N) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (k : K ⧸ N)
    rwa [hx] at h
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  have hg2 : (k ^ b) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, show b * 2 ^ a = orderOf k by rw [hab, mul_comm], pow_orderOf_eq_one]
  have hgmem : k ^ b ∈ Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1} :=
    Subgroup.subset_closure (⟨a, hg2⟩ : k ^ b ∈ {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1})
  have hgN : k ^ b ∉ N := by
    intro hmem
    have h1 : ((k ^ b : K) : K ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    rw [QuotientGroup.mk_pow, ln_pow_odd_of_sq_eq_one hkk hb] at h1
    have h2 : orderOf (k : K ⧸ N) = 1 := by rw [h1, orderOf_one]
    exact absurd (hx.symm.trans h2) (by norm_num)
  rcases normal_dichotomy hKperf N hNodd hS (Subgroup.closure {k : K | ∃ n : ℕ, k ^ (2 ^ n) = 1})
    with h | h
  · exact h
  · exact absurd (h hgmem) hgN

end CFSG.RankThree.PartTwo.Sec13.F135Last
