module

import CFSG.RankThree.PartTwo.Sec4.Steps444
import CFSG.RankThree.PartTwo.Sec5.Item37
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel isElemAbelian_map)

theorem eq_one_of_pow_prime_pow_eq_one {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {N : Subgroup X} (hN : ¬ p ∣ Nat.card N) {g : X} (hg : g ∈ N) {a : ℕ}
    (hga : g ^ (p ^ a) = 1) : g = 1 := by
  have h1 : orderOf g ∣ p ^ a := orderOf_dvd_of_pow_eq_one hga
  have h2 : orderOf g ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ a) (Nat.card N) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  have h3 : orderOf g ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem exists_lift_pow_three_eq_one {X : Type*} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {A : Subgroup X} (hA : IsPGroup 3 A) {x : X ⧸ N}
    (hx : x ∈ Subgroup.centralizer (A.map (QuotientGroup.mk' N) : Set (X ⧸ N)))
    (hx3 : x ^ 3 = 1) :
    ∃ y ∈ Subgroup.centralizer (A : Set X), y ^ 3 = 1 ∧ QuotientGroup.mk' N y = x := by
  obtain ⟨y, hyC, hy⟩ :=
    exists_centralizer_preimage_of_pGroup_prime_complement_kernel 3 Nat.prime_three
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk'])
      A hA x hx
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨e, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hmod : m * (m % 3) % 3 = 1 := by
    have h3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h3 with h | h <;> rw [Nat.mul_mod, h]
  set w := y ^ (m * (m % 3)) with hw
  have hwC : w ∈ Subgroup.centralizer (A : Set X) := Subgroup.pow_mem _ hyC _
  have hwx : QuotientGroup.mk' N w = x := by
    rw [hw, map_pow, hy, pow_eq_pow_mod _ hx3, hmod, pow_one]
  have hw3e : w ^ (3 ^ e) = 1 := by
    rw [hw, ← pow_mul, show m * (m % 3) * 3 ^ e = (3 ^ e * m) * (m % 3) by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]
  refine ⟨w, hwC, ?_, hwx⟩
  have hmem : w ^ 3 ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_pow, hwx, hx3]
  refine eq_one_of_pow_prime_pow_eq_one Nat.prime_three hN hmem (a := e) ?_
  rw [pow_right_comm, hw3e, one_pow]

theorem commutator_eq_bot_of_bender_quotient {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ y ∈ Subgroup.centralizer (A : Set X), y ^ 3 = 1 → y ∈ A)
    {N : Subgroup X} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {S P : Subgroup (X ⧸ N)}
    (hS : ¬ 3 ∣ Nat.card S)
    (hAS : A.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (S : Set (X ⧸ N)))
    (hP : IsPGroup 3 P)
    (hAP : A.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (P : Set (X ⧸ N)))
    (hSP : S ≤ Subgroup.normalizer (P : Set (X ⧸ N))) : ⁅P, S⁆ = ⊥ := by
  have hApg : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  refine Sec5.rank3II_3_7 (X ⧸ N) 3 Nat.prime_three (by norm_num) (A.map (QuotientGroup.mk' N))
    S P (isElemAbelian_map 3 _ A hA) hS hAS hP hAP hSP
    fun y hy hy3 => ?_
  obtain ⟨w, hwC, hw3, rfl⟩ := exists_lift_pow_three_eq_one hN hApg hy.2 hy3
  exact Subgroup.mem_map_of_mem _ (hA3 w hwC hw3)

theorem le_pPrimeCore_of_bender {X : Type} [Group X] [Finite X]
    (hX : CFSG.HallHigman.IsPSolvable 3 X) {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ y ∈ Subgroup.centralizer (A : Set X), y ^ 3 = 1 → y ∈ A) {Y : Subgroup X}
    (hY : ¬ 3 ∣ Nat.card Y) (hAY : A ≤ Subgroup.normalizer (Y : Set X)) :
    Y ≤ CFSG.pPrimeCore 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pPrimeCore 3 X with hNdef
  have hN : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  set π := QuotientGroup.mk' N
  set P := CFSG.pCore 3 (X ⧸ N)
  have hPtop : Subgroup.normalizer (P : Set (X ⧸ N)) = ⊤ := Subgroup.normalizer_eq_top P
  have hS : ¬ 3 ∣ Nat.card (Y.map π) := fun h => hY (h.trans (Subgroup.card_map_dvd Y π))
  have hAS : A.map π ≤ Subgroup.normalizer ((Y.map π : Subgroup (X ⧸ N)) : Set (X ⧸ N)) :=
    (Subgroup.map_mono hAY).trans (Subgroup.le_normalizer_map π)
  have hcomm : ⁅P, Y.map π⁆ = ⊥ :=
    commutator_eq_bot_of_bender_quotient hA hA3 hN hS hAS CFSG.pCore_isPGroup
      (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
  have hYC : Y.map π ≤ Subgroup.centralizer (P : Set (X ⧸ N)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm, hcomm]
  have hHH : Subgroup.centralizer (P : Set (X ⧸ N)) ≤ P := by
    have hsep := (CFSG.HallHigman.isPiSeparable_of_isPSolvable Nat.prime_three hX).quotient N
    have hcore : piCore {q : Nat.Primes | q.val = 3}ᶜ (X ⧸ N) = ⊥ := by
      rw [← CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := X) 3, pPrimeCore_eq_piCore]
      rfl
    have h := CFSG.HallHigman.centralizer_piCore_le_piCore hsep hcore
    rwa [← pCore_eq_piCore] at h
  have hYP : IsPGroup 3 (Y.map π) := CFSG.pCore_isPGroup.to_le (hYC.trans hHH)
  have hbot : Y.map π = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYP
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero])
    · exact (hS (by rw [hk]; exact dvd_pow_self 3 (Nat.succ_ne_zero k))).elim
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem maxInvariantPiSubgroups_eq_pPrimeCore {G : Type} [Group G] [Finite G] {A H : Subgroup G}
    (hAH : A ≤ H) (hH : CFSG.HallHigman.IsPSolvable 3 H) (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A) :
    maxInvariantPiSubgroups H A (piCompl 3) = {inSubgroup (CFSG.pPrimeCore 3) H} := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := inSubgroup (CFSG.pPrimeCore 3) H with hOdef
  have hOmem : O ∈ invariantPiSubgroups H A (piCompl 3) := by
    rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
    refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [hOdef, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
    · have h := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore 3 H) H.subtype
      rw [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h
      exact hAH.trans h
  have hle : ∀ Y ∈ invariantPiSubgroups H A (piCompl 3), Y ≤ O := by
    intro Y hYmem
    rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three] at hYmem
    obtain ⟨hYH, hY3, hAY⟩ := hYmem
    have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf H) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · have h := hA.1.is_comm.comm (⟨((a : H) : G), a.2⟩ : A) ⟨((b : H) : G), b.2⟩
        simpa using congrArg Subtype.val h
      · have h3 := hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
        simpa using h3
    have hA3' : ∀ y ∈ Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H), y ^ 3 = 1 →
        y ∈ A.subgroupOf H := by
      intro y hy hy3
      have hy3' : (y : G) ^ 3 = 1 := by
        have h := congrArg Subtype.val hy3
        simpa using h
      refine Subgroup.mem_subgroupOf.mpr (hA3 y ?_ hy3')
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := Subgroup.mem_centralizer_iff.mp hy ⟨a, hAH ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      exact congrArg Subtype.val h
    have hY' : ¬ 3 ∣ Nat.card (Y.subgroupOf H) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]
    have hAY' : A.subgroupOf H ≤ Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h := Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp ha)) y
      simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_inv] using h
    have h := le_pPrimeCore_of_bender hH hA' hA3' hY' hAY'
    rw [← Subgroup.map_subgroupOf_eq_of_le hYH]
    exact Subgroup.map_mono h
  ext Y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hY
    exact le_antisymm (hle Y hY.1) (hY.2 hOmem (hle Y hY.1))
  · rintro rfl
    exact ⟨hOmem, fun Z hZ _ => hle Z hZ⟩

theorem rank3II_4_37 :
    ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q →
      ∀ H : Subgroup G, A ≤ H → CFSG.HallHigman.IsPSolvable 3 H →
        maxInvariantPiSubgroups H A (piCompl 3) = {inSubgroup (CFSG.pPrimeCore 3) H} :=
  fun G _ _ A M Q h _ hAH hH =>
  maxInvariantPiSubgroups_eq_pPrimeCore hAH hH h.isE27.1
    fun _ hx hx3 => rank3II_4_35 G A M Q h _ hx hx3

theorem rank3II_4_46 :
    ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
      ∀ X : Subgroup G, A ≤ X → CFSG.HallHigman.IsPSolvable 3 X →
        maxInvariantPiSubgroups X A (piCompl 3) = {inSubgroup (CFSG.pPrimeCore 3) X} :=
  fun G _ _ A M h _ hAX hX =>
  maxInvariantPiSubgroups_eq_pPrimeCore hAX hX h.isE27.1
    fun _ hx hx3 => rank3II_4_45 G A M h _ hx hx3

theorem map_le_centralizer_pCore_of_bender {G : Type} [Group G] [Finite G] {A Q : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    Q.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) ≤
      Subgroup.centralizer (CFSG.pCore 3 (G ⧸ CFSG.pPrimeCore 3 G) : Set (G ⧸ CFSG.pPrimeCore 3 G))
    := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 G) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  set P := CFSG.pCore 3 (G ⧸ CFSG.pPrimeCore 3 G)
  have hPtop : Subgroup.normalizer (P : Set (G ⧸ CFSG.pPrimeCore 3 G)) = ⊤ :=
    Subgroup.normalizer_eq_top P
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 G)
  have hS : ¬ 3 ∣ Nat.card (Q.map π) := fun h => hQ (h.trans (Subgroup.card_map_dvd Q _))
  have hAS : A.map π ≤
      Subgroup.normalizer ((Q.map π : Subgroup _) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (Subgroup.map_mono hAQ).trans (Subgroup.le_normalizer_map _)
  have hcomm : ⁅P, Q.map π⁆ = ⊥ :=
    commutator_eq_bot_of_bender_quotient hA hA3 hN hS hAS CFSG.pCore_isPGroup
      (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm, hcomm]

theorem rank3II_4_48 :
    ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M →
      (inSubgroup (CFSG.pPrimeCore 3) M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) ≤
        Subgroup.centralizer
          (CFSG.pCore 3 (G ⧸ CFSG.pPrimeCore 3 G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
  fun G _ _ A M h => by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := h.isE27.le_gamma.trans h.gamma_le
  refine map_le_centralizer_pCore_of_bender h.isE27.1
    (fun _ hx hx3 => rank3II_4_45 G A M h _ hx hx3) ?_ ?_
  · rw [inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  · have h' := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore 3 M) M.subtype
    rw [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h'
    exact hAM.trans h'

end CFSG.RankThree.PartTwo.Sec4
