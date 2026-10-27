module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res4

open Equiv

theorem card_centralizer_perm_ten_of_pow_three {σ : Perm (Fin 10)} (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ σ.cycleType.sum = 3 * k ∧
      Nat.card (Subgroup.centralizer {σ}) = (10 - 3 * k).factorial * 3 ^ k * k.factorial := by
  have hmem : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have hdvd : n ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h3)
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · omega
    · exact h
  set k := Multiset.card σ.cycleType with hk
  have hrep : σ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hk1 : 1 ≤ k := by
    by_contra h0
    exact h1 (Equiv.Perm.card_cycleType_eq_zero.mp (by omega))
  have hsum : σ.cycleType.sum = 3 * k := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : σ.cycleType.sum ≤ 10 := by
    have := Equiv.Perm.sum_cycleType_le σ
    rwa [Fintype.card_fin] at this
  refine ⟨k, hk1, by omega, hsum, ?_⟩
  rw [Equiv.Perm.nat_card_centralizer, Fintype.card_fin, hsum, hrep, Multiset.prod_replicate,
    Multiset.toFinset_replicate, ite_eq_right_iff.mpr (by omega), Finset.prod_singleton,
    Multiset.count_replicate_self]

theorem card_sup_dvd_of_le_normalizer {G : Type*} [Group G] [Finite G] (N I : Subgroup G)
    (hI : I ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2

theorem centralizer_le_zpowers_sup_of_a10 {X : Type*} [Group X] [Finite X]
    (φ : X ≃* alternatingGroup (Fin 10)) {x : X} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {K : Subgroup X} (hK : Nonempty (K ≃* alternatingGroup (Fin 7)))
    (hKx : K ≤ Subgroup.centralizer {x}) :
    Subgroup.centralizer {x} ≤ K ⊔ Subgroup.zpowers x := by
  classical
  obtain ⟨ψ⟩ := hK
  set ι : X →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp φ.toMonoidHom with hιdef
  have hιinj : Function.Injective ι :=
    (alternatingGroup (Fin 10)).subtype_injective.comp φ.injective
  set σ := ι x with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hx3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hx1 (hιinj (h.trans (map_one ι).symm))
  obtain ⟨k, hk1, hk3, hsum, hcard⟩ := card_centralizer_perm_ten_of_pow_three hσ3 hσ1
  set C := Subgroup.centralizer ({x} : Set X) with hC
  have hCmap : C.map ι ≤ Subgroup.centralizer {σ} := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ({x} : Set X) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc' ⊢
    rw [hσ, ← map_mul, ← map_mul, hc']
  have hCalt : C.map ι ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨c, -, rfl⟩
    exact (φ c).2
  have hcardC : Nat.card C = Nat.card (C.map ι) :=
    (Subgroup.card_map_of_injective hιinj).symm
  have hCdvd : Nat.card C ∣ (10 - 3 * k).factorial * 3 ^ k * k.factorial := by
    rw [hcardC, ← hcard]
    exact Subgroup.card_dvd_of_le hCmap
  have hK7 : Nat.card K = 2520 := by
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hxK : x ∉ K := by
    intro hxK
    have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
      alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have hmem : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKx y.2)
    have h1 : ψ ⟨x, hxK⟩ ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
      rw [Subgroup.mem_center_iff] at hmem ⊢
      intro z
      obtain ⟨y, rfl⟩ := ψ.surjective z
      rw [← map_mul, ← map_mul, hmem y]
    rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
    exact hx1 (congrArg Subtype.val h1)
  set M := K ⊔ Subgroup.zpowers x with hM
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (K : Set X) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKx hy)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hMdvd : Nat.card M ∣ 2520 * 3 := by
    have := card_sup_dvd_of_le_normalizer K (Subgroup.zpowers x) hxN
    rwa [hK7, Nat.card_zpowers, hox] at this
  have hKM : K ≤ M := le_sup_left
  have h2520 : 2520 ∣ Nat.card M := hK7 ▸ Subgroup.card_dvd_of_le hKM
  have hM7560 : Nat.card M = 7560 := by
    obtain ⟨d, hd⟩ := h2520
    have hd3 : d ∣ 3 := by
      rw [hd] at hMdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hMdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with rfl | rfl
    · exfalso
      have hMK : M = K := (Subgroup.eq_of_le_of_card_ge hKM (by rw [hd, hK7])).symm
      exact hxK (hMK ▸ (le_sup_right : Subgroup.zpowers x ≤ M) (Subgroup.mem_zpowers x))
    · rw [hd]
  have hMC : M ≤ C :=
    sup_le hKx (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have h7560 : 7560 ∣ Nat.card C := hM7560 ▸ Subgroup.card_dvd_of_le hMC
  have hk : k = 1 := by
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with h | h | h
    · exact h
    · exfalso
      rw [h] at hCdvd
      have := h7560.trans hCdvd
      norm_num [Nat.factorial] at this
    · exfalso
      rw [h] at hCdvd
      have := h7560.trans hCdvd
      norm_num [Nat.factorial] at this
  subst hk
  have hnot : ¬ Subgroup.centralizer {σ} ≤ alternatingGroup (Fin 10) := by
    intro hle
    have := Equiv.Perm.card_le_of_centralizer_le_alternating hle
    rw [Fintype.card_fin, hsum] at this
    omega
  have hne : C.map ι ≠ Subgroup.centralizer {σ} := fun h => hnot (h ▸ hCalt)
  have hClt : Nat.card C ≠ 15120 := by
    intro h
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hCmap ?_
    rw [← hcardC, h, hcard]
    norm_num [Nat.factorial]
  have hC7560 : Nat.card C = 7560 := by
    have hdvd : Nat.card C ∣ 15120 := by
      have := hCdvd
      norm_num [Nat.factorial] at this
      exact this
    obtain ⟨m, hm⟩ := h7560
    rw [hm] at hdvd hClt ⊢
    have hm2 : m ∣ 2 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7560) (show 7560 * m ∣ 7560 * 2 from hdvd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with rfl | rfl
    · rfl
    · exact absurd rfl hClt
  have hCM : C = M := (Subgroup.eq_of_le_of_card_ge hMC (by rw [hC7560, hM7560])).symm
  rw [hCM]

end CFSG.RankThree.PartTwo.Sec14.Item148Res4
