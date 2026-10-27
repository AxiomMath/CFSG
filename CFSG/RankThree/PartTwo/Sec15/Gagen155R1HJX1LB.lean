module

public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_pCore_two_of_mem_sylow_three {L : Subgroup G} {x : ↥L}
    (hx2 : x ∈ CFSG.pCore 2 ↥L) {S : Sylow 3 ↥L} (hx3 : x ∈ (S : Subgroup ↥L)) : x = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hx2⟩
  obtain ⟨m, hm⟩ := (Sylow.isPGroup' S) ⟨x, hx3⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hm' : x ^ 3 ^ m = 1 := congrArg Subtype.val hm
  have hcop23 : Nat.Coprime 2 3 := by norm_num
  have hcop2 : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k hcop23
  have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow_right m hcop2
  have h1 : x ^ Nat.gcd (2 ^ k) (3 ^ m) = 1 := pow_gcd_eq_one.mpr ⟨hk', hm'⟩
  rwa [hcop, pow_one] at h1

theorem not_seven_dvd_card_of_map_le_centralizer {L : Subgroup G} {X : Type*} [Group X] [Finite X]
    (M : Subgroup ↥L) (π : ↥L →* X) {z : X}
    (hrange : (π.comp M.subtype).range ≤ Subgroup.centralizer ({z} : Set X))
    (hC : Nat.card ↥(Subgroup.centralizer ({z} : Set X)) = 1080)
    (hker : IsPGroup 2 (π.comp M.subtype).ker) : ¬ 7 ∣ Nat.card M := by
  let f := π.comp M.subtype
  have hcard := Subgroup.card_ker_mul_card_range f
  have hr : Nat.card f.range ∣ 1080 := hC ▸ Subgroup.card_dvd_of_le hrange
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  intro h7
  rw [← hcard, hk] at h7
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 7) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h)
    omega
  · exact absurd (h.trans hr) (by norm_num)

theorem not_seven_dvd_card_inf_centralizer (h415 : Sec4.Item4_15) {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) {d : G}
    (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hdc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    ¬ 7 ∣ Nat.card ↥(L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  obtain ⟨S, hdS, hSd⟩ := hdc
  set P := CFSG.pCore 2 ↥L with hP
  set π : ↥L →* ↥L ⧸ P := QuotientGroup.mk' P with hπ
  set z : ↥L ⧸ P := π ⟨d, hdL⟩ with hz
  have hz1 : z ≠ 1 := by
    intro h
    have hx2 : (⟨d, hdL⟩ : ↥L) ∈ P := (QuotientGroup.eq_one_iff _).mp h
    have hx1 := eq_one_of_mem_pCore_two_of_mem_sylow_three (L := L) hx2 hdS
    exact hd1 (congrArg Subtype.val hx1)
  have hzS : ∃ P' : Sylow 3 (↥L ⧸ P), z ∈ (P' : Subgroup (↥L ⧸ P)) ∧
      (P' : Subgroup (↥L ⧸ P)) ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ P)) := by
    refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective P), ⟨⟨d, hdL⟩, hdS, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsd := Subgroup.mem_centralizer_singleton_iff.mp (hSd hs)
    change π s * π ⟨d, hdL⟩ = π ⟨d, hdL⟩ * π s
    rw [← map_mul, ← map_mul, hsd]
  obtain ⟨φ⟩ := hJ
  have hC := KFacts.KS14.j2_centralizer_isTripleCover h415 ⟨φ⟩ hz1 hzS
  have hC1080 : Nat.card ↥(Subgroup.centralizer ({z} : Set (↥L ⧸ P))) = 1080 := by
    obtain ⟨hc, ⟨e⟩⟩ := hC
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _),
      Nat.card_congr e.toEquiv, hc, KFacts.KS14.card_alternatingGroup_six]
  set M : Subgroup ↥L := (Subgroup.centralizer ({d} : Set G)).subgroupOf L with hM
  have hMcard : Nat.card M = Nat.card ↥(L ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [hM, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let f : ↥M →* ↥L ⧸ P := π.comp M.subtype
  have hrange : f.range ≤ Subgroup.centralizer ({z} : Set (↥L ⧸ P)) := by
    rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hm : ((m : ↥L) : G) ∈ Subgroup.centralizer ({d} : Set G) := m.2
    have hmd := Subgroup.mem_centralizer_singleton_iff.mp hm
    change π m * π ⟨d, hdL⟩ = π ⟨d, hdL⟩ * π m
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hmd
  have hker : IsPGroup 2 f.ker := by
    intro x
    have hx : f x = 1 := x.2
    have hxP : ((x : ↥M) : ↥L) ∈ P := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hnotM := not_seven_dvd_card_of_map_le_centralizer M π (z := z) hrange hC1080 hker
  rwa [← hMcard]

theorem isLBConfig_d_ne_one_of_omegaA_singleton {A B : Subgroup G} {c b₀ d₀ : G}
    {L₀ : Subgroup G} (hΩ : omegaA A = {Subgroup.zpowers c}) (hc₀ : IsLBConfig A B b₀ d₀ L₀)
    {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) (hac : Subgroup.zpowers a ≠ Subgroup.zpowers c) :
    d₀ ≠ 1 := by
  rintro rfl
  have hBz : B = Subgroup.zpowers b₀ := by
    rw [hc₀.1, Sec14.closure_pair_eq_sup, Subgroup.zpowers_one_eq_bot]
    simp
  have hzbc : Subgroup.zpowers b₀ = Subgroup.zpowers c := by
    have hmem := hc₀.2.1
    rw [hΩ] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have haz : a ∈ Subgroup.zpowers c := by
    rw [← hzbc, ← hBz]
    exact haB
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by
    have hmem : Subgroup.zpowers c ∈ omegaA A := by
      rw [hΩ]
      simp
    exact (mem_omegaA_iff.mp hmem).2.1
  have hdvd : orderOf a ∣ 3 := by
    rw [← hcard]
    exact Subgroup.orderOf_dvd_natCard (Subgroup.zpowers c) haz
  have hord : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h3
  have hza : Subgroup.zpowers a ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr haz
  have hcarda : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hord]
  exact hac (Subgroup.eq_of_le_of_card_ge hza (by rw [hcard, hcarda]))

theorem isLBConfig_eq_of_omegaA_singleton {A B : Subgroup G} {c : G}
    (hΩ : omegaA A = {Subgroup.zpowers c}) {b₀ d₀ : G} {L₀ : Subgroup G}
    (hc₀ : IsLBConfig A B b₀ d₀ L₀) {b' d' : G} {L' : Subgroup G}
    (hc' : IsLBConfig A B b' d' L') : L' = L₀ := by
  have hz : Subgroup.zpowers b' = Subgroup.zpowers b₀ := by
    have h1 := hc'.2.1
    have h2 := hc₀.2.1
    rw [hΩ] at h1 h2
    rw [Set.mem_singleton_iff.mp h1, Set.mem_singleton_iff.mp h2]
  have hla := lA_eq_of_zpowers_eq (A := A) hz
  have hsingle : ({L'} : Set (Subgroup G)) = {L₀} := by
    rw [← hc'.2.2.1, hla, hc₀.2.2.1]
  exact Set.singleton_injective hsingle

theorem not_seven_dvd_card_lB (h415 : Sec4.Item4_15) {A : Subgroup G} {c : G}
    (hΩ : omegaA A = {Subgroup.zpowers c}) {a b : G} (ha1 : a ≠ 1)
    (hac : Subgroup.zpowers a ≠ Subgroup.zpowers c) :
    ¬ 7 ∣ Nat.card ↥(lB A (Subgroup.closure {a, b})) := by
  classical
  by_cases hcon : ∃ b' d' L', IsLBConfig A (Subgroup.closure {a, b}) b' d' L'
  · obtain ⟨b₀, d₀, L₀, hc₀⟩ := hcon
    have haB : a ∈ Subgroup.closure ({a, b} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert a {b})
    have hd0 : d₀ ≠ 1 :=
      isLBConfig_d_ne_one_of_omegaA_singleton (B := Subgroup.closure {a, b}) (b₀ := b₀)
        hΩ hc₀ haB ha1 hac
    have hLuniq : ∀ (b' d' : G) (L' : Subgroup G),
        IsLBConfig A (Subgroup.closure {a, b}) b' d' L' → L' = L₀ :=
      fun b' d' L' hc' => isLBConfig_eq_of_omegaA_singleton
        (B := Subgroup.closure {a, b}) (b₀ := b₀) hΩ hc₀ hc'
    have hLBleL : lB A (Subgroup.closure {a, b}) ≤ L₀ := by
      refine iSup_le fun b' => iSup_le fun d' => iSup_le fun L' => iSup_le fun hc' => ?_
      rw [hLuniq b' d' L' hc']
      exact (Subgroup.map_subtype_le _).trans inf_le_left
    have hdB : d₀ ∈ Subgroup.closure ({a, b} : Set G) := by
      rw [hc₀.1]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem b₀ rfl)
    have hLBleC : lB A (Subgroup.closure {a, b}) ≤
        Subgroup.centralizer ({d₀} : Set G) :=
      (lB_le_centralizer A _).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB))
    have hLBle : lB A (Subgroup.closure {a, b}) ≤
        L₀ ⊓ Subgroup.centralizer ({d₀} : Set G) :=
      le_inf hLBleL hLBleC
    obtain ⟨hdL₀, S₀, hdS₀, hSd₀⟩ := hc₀.2.2.2.2
    have hnot :=
      CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1.not_seven_dvd_card_inf_centralizer
        (L := L₀) h415 hc₀.2.2.2.1 hdL₀ hd0 ⟨S₀, hdS₀, hSd₀⟩
    exact fun h7 => hnot (h7.trans (Subgroup.card_dvd_of_le hLBle))
  · have hbot : lB A (Subgroup.closure {a, b}) = ⊥ :=
      lB_eq_bot (B := Subgroup.closure {a, b}) fun b' d' L' hc => hcon ⟨b', d', L', hc⟩
    rw [hbot, Subgroup.card_bot]
    norm_num

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1
