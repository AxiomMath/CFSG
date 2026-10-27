module

public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
import CFSG.RankThree.PartTwo.Sec18.Item188Abs
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item188Proof

open CFSG

theorem subgroupOf_le_normalizer_subgroupOf {G : Type} [Group G] {M A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    A.subgroupOf M ≤ Subgroup.normalizer ((B.subgroupOf M : Subgroup M) : Set M) := by
  intro a ha
  have ha' : (a : G) ∈ A := ha
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  have key := Subgroup.mem_normalizer_iff.mp (hAB ha') (h : G)
  simpa [Subgroup.mem_subgroupOf] using key

theorem mem_map_of_commute_of_coprime {G : Type} [Group G] [Finite G] {M A : Subgroup G}
    {N : Subgroup M} [N.Normal] (hN : Nat.Coprime 3 (Nat.card N)) (hAM : A ≤ M)
    (hA3 : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A)
    (hAM3 : IsPGroup 3 (A.subgroupOf M)) {x : M ⧸ N} (hx3 : x ^ 3 = 1)
    (hx : ∀ a ∈ (A.subgroupOf M).map (QuotientGroup.mk' N), a * x = x * a) :
    x ∈ (A.subgroupOf M).map (QuotientGroup.mk' N) := by
  set π : M →* M ⧸ N := QuotientGroup.mk' N with hπ
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN h
  have hcent :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      3 Nat.prime_three π (QuotientGroup.mk'_surjective N) hker (A.subgroupOf M) hAM3
  have hxC : x ∈ Subgroup.centralizer
      (((A.subgroupOf M).map π : Subgroup (M ⧸ N)) : Set (M ⧸ N)) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => hx a ha
  rw [← hcent] at hxC
  obtain ⟨g, hg, rfl⟩ := hxC
  obtain ⟨e, m, hm3, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hge : (g ^ m) ^ (3 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hπ3 : π ((g ^ m) ^ 3) = 1 := by
    rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have hhN : (g ^ m) ^ 3 ∈ N := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ3
    exact hπ3
  have h3e : ((g ^ m) ^ 3) ^ (3 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hge, one_pow]
  have hord : orderOf ((g ^ m) ^ 3) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left e hN) (orderOf_dvd_of_pow_eq_one h3e)
      (Subgroup.orderOf_dvd_natCard N hhN)
  have hh3 : (g ^ m) ^ 3 = 1 := orderOf_eq_one_iff.mp hord
  have hgA : ((g ^ m : M) : G) ∈ A := by
    refine hA3 ((g ^ m : M) : G) ?_ fun a ha => ?_
    · simpa using congrArg Subtype.val hh3
    · have haM : a ∈ M := hAM ha
      have hcomm : (⟨a, haM⟩ : M) * g = g * ⟨a, haM⟩ :=
        Subgroup.mem_centralizer_iff.mp hg ⟨a, haM⟩ (Subgroup.mem_subgroupOf.mpr ha)
      have h1 : (⟨a, haM⟩ : M) * g ^ m = g ^ m * ⟨a, haM⟩ :=
        ((show Commute (⟨a, haM⟩ : M) g from hcomm).pow_right m).eq
      exact congrArg Subtype.val h1
  have hgmA : g ^ m ∈ A.subgroupOf M := Subgroup.mem_subgroupOf.mpr hgA
  have hzm : π g ^ m ∈ (A.subgroupOf M).map π := ⟨g ^ m, hgmA, by rw [map_pow]⟩
  have hmm : (m * m) % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
  have hzz : (π g ^ m) ^ m = π g := by
    rw [← pow_mul, ← Nat.mod_add_div (m * m) 3, hmm, pow_add, pow_mul, hx3, one_pow, mul_one,
      pow_one]
  rw [← hzz]
  exact Subgroup.pow_mem _ hzm _

theorem le_map_of_normal_coprime {G : Type} [Group G] [Finite G] {M A P T : Subgroup G}
    {N : Subgroup M} [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    (hCQ : Subgroup.centralizer (CFSG.pCore 3 (M ⧸ N) : Set (M ⧸ N)) ≤ CFSG.pCore 3 (M ⧸ N))
    (hP3 : IsPGroup 3 P) (hPM : P ≤ M) (hPdvd : ¬ 3 ∣ P.relIndex M) (hAP : A ≤ P)
    (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hA3 : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A)
    (hT : IsPGroup 2 T) (hTM : T ≤ M) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ N.map M.subtype := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : M →* M ⧸ N := QuotientGroup.mk' N with hπ
  have hAM : A ≤ M := hAP.trans hPM
  have hAM3 : IsPGroup 3 (A.subgroupOf M) := (hP3.to_le hAP).comap_subtype
  have hTM2 : IsPGroup 2 (T.subgroupOf M) := hT.comap_subtype
  have hPM3 : IsPGroup 3 (P.subgroupOf M) := hP3.comap_subtype
  have hA'3 : IsPGroup 3 ((A.subgroupOf M).map π) := hAM3.map π
  have hT'2 : IsPGroup 2 ((T.subgroupOf M).map π) := hTM2.map π
  have hP'3 : IsPGroup 3 ((P.subgroupOf M).map π) := hPM3.map π
  have hP'dvd : ¬ 3 ∣ ((P.subgroupOf M).map π).index := fun h =>
    hPdvd (dvd_trans h ((P.subgroupOf M).index_map_dvd (QuotientGroup.mk'_surjective N)))
  have hA'T : (A.subgroupOf M).map π ≤
      Subgroup.normalizer (((T.subgroupOf M).map π : Subgroup (M ⧸ N)) : Set (M ⧸ N)) :=
    (Subgroup.map_mono (f := π) (subgroupOf_le_normalizer_subgroupOf (M := M) hAT)).trans
      (Subgroup.le_normalizer_map π)
  have hP'A : (P.subgroupOf M).map π ≤
      Subgroup.normalizer (((A.subgroupOf M).map π : Subgroup (M ⧸ N)) : Set (M ⧸ N)) :=
    (Subgroup.map_mono (f := π) (subgroupOf_le_normalizer_subgroupOf (M := M) hPA)).trans
      (Subgroup.le_normalizer_map π)
  have hQP : CFSG.pCore 3 (M ⧸ N) ≤ (P.subgroupOf M).map π := by
    have h := (CFSG.pCore_isPGroup (p := 3) (G := M ⧸ N)).le_sylow_of_normal
      (hP'3.toSylow hP'dvd)
    rwa [IsPGroup.toSylow_coe] at h
  have hbot : (T.subgroupOf M).map π = ⊥ :=
    eq_bot_of_isPGroup_two (CFSG.pCore_isPGroup (p := 3) (G := M ⧸ N)) inferInstance hCQ hA'3
      (hQP.trans hP'A) (fun _ _ hx3 hx => mem_map_of_commute_of_coprime hN hAM hA3 hAM3 hx3 hx)
      hT'2 hA'T
  intro t ht
  have hmem : π ⟨t, hTM ht⟩ ∈ (T.subgroupOf M).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ht)
  rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  simpa using Subgroup.mem_map_of_mem M.subtype hmem

theorem le_inSubgroup_pPrimeCore_of_isPConstrained {G : Type} [Group G] [Finite G]
    {M A P T : Subgroup G} (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M) (hAP : A ≤ P)
    (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hA3 : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A)
    (hT : IsPGroup 2 T) (hTM : T ≤ M) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ inSubgroup (CFSG.pPrimeCore 3) M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPM, hP3, hPdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).mp hP
  have hN : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥M)) := pPrimeCore_coprime_card
  exact le_map_of_normal_coprime hN
    (CFSG.ABGTheoremB.RelativeZJ.centralizer_pCore_quotient_le hcon)
    hP3 hPM hPdvd hAP hPA hA3 hT hTM hAT

end CFSG.RankThree.PartTwo.Sec18.Item188Proof
