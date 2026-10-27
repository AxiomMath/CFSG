module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH2A8
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier

public section

namespace CFSG.StandardType

section A8Numerics

variable {G : Type} [Group G] [Finite G] {J : Subgroup G}

theorem card_center_dvd_two_of_a3Case (hq : CFSG.Assembly.IsQuasisimple J)
    (hA : GGSixLSevenA3Case J) : Nat.card (Subgroup.center ↥J) ∣ 2 := by
  obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hA
  have hq' : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hq
  have h1 := CFSG.RankThree.PartTwo.KFacts.KS44.card_center_dvd_card_hopfMultiplier hq'
  have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (↥J ⧸ Subgroup.center ↥J)) = 2 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
    exact CFSG.EvenSporadicStandard.M24Std.card_hopfMultiplier_of_alternating_eight e
  rwa [h2] at h1

theorem card_dvd_of_a3Case (hq : CFSG.Assembly.IsQuasisimple J) (hA : GGSixLSevenA3Case J) :
    Nat.card ↥J ∣ 40320 := by
  obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hA
  have hZ := card_center_dvd_two_of_a3Case hq hA
  have hQ : Nat.card (↥J ⧸ Subgroup.center ↥J) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.EvenSporadicStandard.M24Std.card_alternatingGroup_eight
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J), hQ]
  exact (Nat.mul_dvd_mul_left 20160 hZ).trans (by norm_num)

theorem eq_one_of_central_pow_of_a3Case {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : CFSG.Assembly.IsQuasisimple J) (hA : GGSixLSevenA3Case J) :
    ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z ^ p = 1 → z = 1 := by
  intro z hz hc hzp
  have hZ := card_center_dvd_two_of_a3Case hq hA
  set z' : ↥(Subgroup.center ↥J) :=
    ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm⟩ with hz'
  have h1 : orderOf z' ∣ 2 := (orderOf_dvd_natCard z').trans hZ
  have h2 : orderOf z' ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext (by simpa using hzp)))
  have h3 : orderOf z' ∣ Nat.gcd p 2 := Nat.dvd_gcd h2 h1
  have hg : Nat.gcd p 2 = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact congrArg (fun w : ↥(Subgroup.center ↥J) => ((w : ↥J) : G)) h3

end A8Numerics

section Arithmetic

theorem eq_three_of_sq_dvd_forty_thousand {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ 40320) : p = 3 := by
  have hd : p ∣ 40320 := (dvd_pow_self p two_ne_zero).trans h
  have h40 : (40320 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [h40] at hd h
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd1 | hd1
  · rcases (Nat.Prime.dvd_mul hp).1 hd1 with hd2 | hd2
    · rcases (Nat.Prime.dvd_mul hp).1 hd2 with hd3 | hd3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow hd3)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd3)
    · have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd2
      subst h5
      norm_num at h
  · have h7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd1
    subst h7
    norm_num at h

theorem not_three_pow_three_dvd_forty_thousand : ¬ 3 ^ 3 ∣ 40320 := by norm_num

theorem not_prime_pow_three_dvd_forty_thousand {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ 40320 := by
  intro h
  have h2 : p ^ 2 ∣ 40320 := (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans h
  have h3 := eq_three_of_sq_dvd_forty_thousand hp hp2 h2
  subst h3
  exact not_three_pow_three_dvd_forty_thousand h

end Arithmetic

section ElementaryAbelian

variable {G : Type*} [Group G] [Finite G]

theorem pow_dvd_card_of_pow_le_card_inf {p k : ℕ} (hp : p.Prime) {A J : Subgroup G}
    (hA : ∀ a ∈ A, a ^ p = 1) (h : p ^ k ≤ Nat.card ↥(A ⊓ J)) : p ^ k ∣ Nat.card ↥J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p ↥(A ⊓ J) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hA g (Subgroup.mem_inf.mp g.2).1
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  rw [hm] at h
  have hkm : k ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have h1 : p ^ k ∣ Nat.card ↥(A ⊓ J) := hm ▸ pow_dvd_pow p hkm
  exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)

end ElementaryAbelian

end CFSG.StandardType
