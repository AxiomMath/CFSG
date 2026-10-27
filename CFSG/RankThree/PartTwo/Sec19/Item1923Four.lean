module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec19.Item194Five

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem step1923_four_card_ne (n : ℕ) (hn : Odd n) :
    Nat.card (projSL 3 (GaloisField 2 n)) ≠ 1814400 := by
  intro h
  obtain ⟨m, rfl⟩ := hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have hmul := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd
    (GaloisField 2 (2 * m + 1))
  rw [hq, h] at hmul
  have hmod : 2 ^ (2 * m + 1) % 3 = 2 := by
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have h2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
      rw [pow_succ, pow_mul]; ring
    rw [h2]; omega
  have hg : Nat.gcd 3 (2 ^ (2 * m + 1) - 1) = 1 := by
    have hnd : ¬ 3 ∣ 2 ^ (2 * m + 1) - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd
  rw [hg, mul_one] at hmul
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num at hmul
  · have hq8 : 8 ≤ 2 ^ (2 * m + 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (2 * m + 1) = q at hmul hq8
    have h2q : 64 ≤ q ^ 2 := by nlinarith
    have h3q : 512 ≤ q ^ 3 := by nlinarith
    have h1' : 63 ≤ q ^ 2 - 1 := by omega
    have h2' : 511 ≤ q ^ 3 - 1 := by omega
    have key := Nat.mul_le_mul h3q (Nat.mul_le_mul h1' h2')
    linarith

private theorem step1923_four_false_alt10 {X : Type} [Group X] (hL3 : IsL3OddType X)
    (hA : Nonempty (X ≃* alternatingGroup (Fin 10))) : False := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hL3
  obtain ⟨eA⟩ := hA
  have h1 : Nat.card (projSL 3 (GaloisField 2 n)) = Nat.card X :=
    Nat.card_congr e.toEquiv.symm
  have h2 : Nat.card X = Nat.card (alternatingGroup (Fin 10)) := Nat.card_congr eA.toEquiv
  have h3 : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
    rw [nat_card_alternatingGroup]; simp [Nat.factorial]
  exact step1923_four_card_ne n hn (h1.trans (h2.trans h3))

private theorem step1923_four_orderOf_mk {K : Subgroup G} {c : G} (hcK : c ∈ K)
    (h3 : orderOf c = 3) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : c ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one c
  apply orderOf_eq_prime
  · have hx3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [← map_pow, hx3, map_one]
  · intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hcO : c ∈ CFSG.Open.pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff _).mpr h1
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨c, hcO⟩
    have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by
      rw [← h3]; exact orderOf_dvd_of_pow_eq_one hck
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at this

theorem item1923_four (hkf : KFacts1923) (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) (hK : K ∈ scriptJ M N) (h2 : scriptJ M N = {K})
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)) (hcK : c ∈ K) :
    Sec18.IsMaxParabolicRankTwo (starIm K N) ∧
      (∀ m ∈ M, (∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) → m ∈ N) := by
  obtain ⟨-, hshape⟩ := step1923_list hkf.h194 h hK
  have hcA : c ∈ A := by
    rw [hF.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcN : c ∈ N := h.le_N hcA
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K) ∈ starIm K N :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcN)
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K)) = 3 :=
    step1923_four_orderOf_mk hcK hF.orderOf_c
  have hproper : IsProperParabolic (starIm K N) := by
    rcases hshape with ⟨-, hp⟩ | ⟨hA, -⟩
    · exact hp
    · exact (step1923_four_false_alt10 hL3 hA).elim
  obtain ⟨n, hn, ⟨e⟩⟩ := hL3
  have hmax : Sec18.IsMaxParabolicRankTwo (starIm K N) :=
    ((hkf.kfl3par (K ⧸ CFSG.pCore 2 K) n hn ⟨e⟩).1 (starIm K N) hproper ⟨_, hmem, hord⟩).1
  refine ⟨hmax, fun m hm hmK => Late.Hyp1921.mem_N_of_centralizes_scriptJ h hkf.h316 hm ?_⟩
  intro K' hK'
  rw [h2, Set.mem_singleton_iff] at hK'
  rw [hK']
  exact hmK

end CFSG.RankThree.PartTwo.Late
