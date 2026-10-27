module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calC conjClosure conjSetOf Opp Bar2 barImage IsL2 IsSz)

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_le_opp {M L : Subgroup G} (hL : L ∈ calC M) (hs : IsSimpleGroup (Bar2 L))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card (Bar2 L)) :
    conjClosure M L ≤ Opp r M := by
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hLopp : L ≤ Opp r M := by
    rw [← S17.opp_eq_self_of_calC hL hs hr hr2 hdvd]
    exact s13_Thirteen2_pElementSubgroup_mono hLM
  refine iSup₂_le fun K hK => ?_
  obtain ⟨g, hg, rfl⟩ := hK
  have hN := PartOne.Section9.le_normalizer_opp r M hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hN
  rw [← hN]
  exact Subgroup.map_mono hLopp

theorem mk_not_mem_barImage {M N : Subgroup G} (hMN : pCoreOf 2 M ≤ Subgroup.normalizer (N : Set G))
    {r : ℕ} (hr2 : r ≠ 2) (hr : r.Prime) {x : G} (hxM : x ∈ M) {k : ℕ}
    (hk : orderOf x = r ^ k) (hxN : x ∉ N) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x, hxM⟩ : ↥M) ∉ barImage M N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hmem
  obtain ⟨m, hm, hmx⟩ := hmem
  have ht : m⁻¹ * ⟨x, hxM⟩ ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq).1 hmx
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨_, ht⟩
  set t : G := ((m⁻¹ * ⟨x, hxM⟩ : ↥M) : G) with htdef
  have htj : t ^ 2 ^ j = 1 := by
    have := congrArg (fun u => ((u : ↥M) : G)) (congrArg Subtype.val hj)
    simpa [htdef] using this
  have hxt : x = (m : G) * t := by rw [htdef]; simp
  have hm' : (m : G) ∈ N := hm
  have htN : t ∈ Subgroup.normalizer (N : Set G) := hMN ⟨_, ht, rfl⟩
  have h2 : x ^ 2 ^ j ∈ N := by
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.mul_pow_mul_inv_pow_mem hm' htN (2 ^ j)
    rwa [htj, inv_one, mul_one, ← hxt] at h1
  have hr' : x ^ r ^ k ∈ N := by rw [← hk, pow_orderOf_eq_one]; exact N.one_mem
  have hcop : Nat.Coprime (2 ^ j) (r ^ k) :=
    Nat.Coprime.pow j k ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  have hgcd := Nat.gcd_eq_gcd_ab (2 ^ j) (r ^ k)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
  apply hxN
  have : x = (x ^ 2 ^ j) ^ (Nat.gcdA (2 ^ j) (r ^ k)) *
      (x ^ r ^ k) ^ (Nat.gcdB (2 ^ j) (r ^ k)) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hgcd, zpow_one]
  rw [this]
  exact N.mul_mem (N.zpow_mem h2 _) (N.zpow_mem hr' _)

theorem le_pRank_of_bar2 {M : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {E : Subgroup (Bar2 M)} (hE : IsElemAbelian r E) {k : ℕ} (hk : Nat.card E = r ^ k) :
    k ≤ CFSG.Open.pRank r M := by
  have h1 := CFSG.AGLEmbedding.pRank_barM_eq hr hr2 M M le_rfl
  have htop : CFSG.AGLEmbedding.barM M M = ⊤ := by
    rw [CFSG.AGLEmbedding.barM, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [← h1]
  exact CFSG.SectionRank.le_pRank hr.one_lt (htop ▸ le_top) hE hk

theorem center_barImage_eq_bot {M L : Subgroup G} (hL : L ∈ calC M)
    (hZ : Subgroup.center (Bar2 L) = ⊥) : Subgroup.center ↥(barImage M L) = ⊥ := by
  obtain ⟨e⟩ := s13_bar_equiv hL
  rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]

theorem exists_pow_pow_not_mem {X : Type*} [Group X] {P : Subgroup X} {y : X} {r : ℕ}
    (hyP : y ∉ P) {k : ℕ} (hk : y ^ r ^ k ∈ P) : ∃ j : ℕ, y ^ r ^ j ∉ P ∧ (y ^ r ^ j) ^ r ∈ P := by
  induction k with
  | zero => exact absurd (by simpa using hk) hyP
  | succ k ih =>
    by_cases h : y ^ r ^ k ∈ P
    · exact ih h
    · exact ⟨k, h, by rw [← pow_mul, ← pow_succ]; exact hk⟩

theorem exists_orderOf_mk_eq {M : Subgroup G} {x : G} (hxM : x ∈ M) {r i : ℕ} (hr : r.Prime)
    (hi : orderOf x = r ^ i) :
    ∃ k : ℕ, orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x, hxM⟩ : ↥M)) = r ^ k := by
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x, hxM⟩ : ↥M)) ∣ r ^ i := by
    rw [← hi, ← Subgroup.orderOf_mk x hxM]
    exact orderOf_map_dvd _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr).1 h1
  exact ⟨k, hk⟩

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
