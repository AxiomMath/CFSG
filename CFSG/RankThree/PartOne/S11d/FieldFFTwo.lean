module

public import CFSG.RankThree.PartOne.S11d.FieldKFacts
public import CFSG.RankThree.PartOne.S11d.FieldTwoTransfer
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)

@[expose] def LargeReeNoInvolution : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → LieModel T .twistedF4 0 2 p →
    CFSG.pRank p T ≤ 1 → ∀ d t : T, orderOf d = p → orderOf t = 2 → t * d = d * t → False

@[expose] def OddCenterLie : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → ∀ (t : StatedLieTag) (n m : ℕ),
    5 ≤ m → LieModel (J ⧸ Subgroup.center J) t n 2 m → ¬ 2 ∣ Nat.card (Subgroup.center J)

variable {G : Type} [Group G] [Finite G]

theorem fieldFixedTwoElements_of_tags (hT : ∀ t, TagFixedFacts t) (hR1 : LargeReeNoInvolution)
    (hR3 : OddCenterLie) : FieldFixedTwoElements := by
  intro G _ _ p J u hset hup hrank hpr d hdJ hd1 hdp hud ⟨t, htmem, ht2⟩ g hg hg2
  have hu : u ∈ Subgroup.normalizer (J : Set G) := hset.2.2.2.2.2.2.1
  have hF := fixedFacts_of_fieldAutSetting hT hset hu hup hrank
  have hp : p.Prime := hset.1
  have hp5 : 5 ≤ p := hset.2.1
  have hq : CFSG.IsQuasisimple ↥J := hset.2.2.1
  have hZ : ¬ p ∣ Nat.card (Subgroup.center J) := hset.2.2.2.2.2.1
  obtain ⟨-, -, -, T₀, n, f, hf, hM, -⟩ := hset.2.2.2.2.2.2
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center J) := hR3 ↥J hq T₀ n (p * f) (by nlinarith) hM
  have : Fact p.Prime := ⟨hp⟩
  have hT2 : ∀ x ∈ fixSub (centerQuotientConj J ⟨u, hu⟩), (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ fixRes (centerQuotientConj J ⟨u, hu⟩) := by
    rcases hF.twoElements with h | hTits
    · exact h
    · exfalso
      have htC : t ∈ J ∧ t ∈ Subgroup.centralizer ({d} : Set G) := Subgroup.mem_inf.mp htmem
      have htd : t * d = d * t := Subgroup.mem_centralizer_singleton_iff.mp htC.2
      let dd : ↥J := ⟨d, hdJ⟩
      let tt : ↥J := ⟨t, htC.1⟩
      have hddp : dd ^ p = 1 := Subtype.ext hdp
      have hdd1 : dd ≠ 1 := fun h => hd1 (by simpa [dd] using congrArg Subtype.val h)
      have hdd : orderOf dd = p := orderOf_eq_prime hddp hdd1
      have htt : orderOf tt = 2 := by
        rw [← Subgroup.orderOf_coe tt]
        exact ht2
      have http : tt ^ 2 = 1 := by
        have := pow_orderOf_eq_one tt
        rwa [htt] at this
      have hdb : orderOf (dd : ↥J ⧸ Subgroup.center ↥J) = p := by
        refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hddp]; rfl) fun h1 => hZ ?_
        have hc : dd ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff dd).mp h1
        have h2 := _root_.orderOf_dvd_natCard (⟨dd, hc⟩ : Subgroup.center ↥J)
        rwa [Subgroup.orderOf_mk, hdd] at h2
      have htb : orderOf (tt : ↥J ⧸ Subgroup.center ↥J) = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, http]; rfl) fun h1 => hZ2 ?_
        have hc : tt ∈ Subgroup.center ↥J := (QuotientGroup.eq_one_iff tt).mp h1
        have h2 := _root_.orderOf_dvd_natCard (⟨tt, hc⟩ : Subgroup.center ↥J)
        rwa [Subgroup.orderOf_mk, htt] at h2
      have hcomm : (tt : ↥J ⧸ Subgroup.center ↥J) * dd = dd * (tt : ↥J ⧸ Subgroup.center ↥J) := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext htd)
      have hrk : CFSG.pRank p (↥J ⧸ Subgroup.center ↥J) ≤ 1 := by
        rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
          (Subgroup.center ↥J) hZ, hpr]
      exact hR1 _ p hp hp5 hTits hrk _ _ hdb htb hcomm
  exact twoElement_mem_perfectResidual_of_two hp hZ hZ2 hu hup hT2 hg hg2

end CFSG.RankThree.PartOne.FieldFix
