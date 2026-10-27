module

public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.RankThree.PartOne.Mult.Alternating
public import CFSG.RankThree.PartOne.Mult.Exceptional
public import CFSG.RankThree.PartOne.Mult.Sporadic

public section

namespace CFSG.RankThree.PartOne.Mult

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PartOne
  Subgroup
open CFSG.Blueprint.NativeSporadic (Carrier)

structure SporadicResidualKernelsTrim : Prop where
  co1_five : SporadicKernelTrivial .Co1 5
  co1_seven : SporadicKernelTrivial .Co1 7
  th_five : SporadicKernelTrivial .Th 5
  th_seven : SporadicKernelTrivial .Th 7
  co2_five : SporadicKernelTrivial .Co2 5
  co3_five : SporadicKernelTrivial .Co3 5
  mcl_five : SporadicKernelTrivial .McL 5
  suz_five : SporadicKernelTrivial .Suz 5
  hn_five : SporadicKernelTrivial .HN 5
  ly_five : SporadicKernelTrivial .Ly 5
  on_seven : SporadicKernelTrivial .ONan 7

theorem SporadicResidualKernels.toTrim (h : SporadicResidualKernels) :
    SporadicResidualKernelsTrim :=
  ⟨h.co1_five, h.co1_seven, h.th_five, h.th_seven, h.co2_five, h.co3_five, h.mcl_five, h.suz_five,
    h.hn_five, h.ly_five, h.on_seven⟩

@[expose] def SectionExcluded (s : TauCeti.SporadicName) : Prop :=
  s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M

theorem SporadicResidualKernelsTrim.trivial_of_pair (hres : SporadicResidualKernelsTrim)
    {s : TauCeti.SporadicName} {p : ℕ} (hex : ¬ SectionExcluded s) (h : SporadicResidualPair s p) :
    SporadicKernelTrivial s p := by
  rcases h with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | rfl
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hres.co1_five
    · exact (hex (by simp [SectionExcluded])).elim
    · exact hres.th_five
    · exact (hex (by simp [SectionExcluded])).elim
    · exact hres.co2_five
    · exact hres.co3_five
    · exact (hex (by simp [SectionExcluded])).elim
    · exact (hex (by simp [SectionExcluded])).elim
    · exact hres.mcl_five
    · exact hres.suz_five
    · exact hres.hn_five
    · exact hres.ly_five
  · rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hres.co1_seven
    · exact (hex (by simp [SectionExcluded])).elim
    · exact hres.th_seven
    · exact (hex (by simp [SectionExcluded])).elim
    · exact hres.on_seven
  · exact (hex (by simp [SectionExcluded])).elim

theorem sec6Eight_of_residual_trim
    
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hres : SporadicResidualKernelsTrim)
    (hFi22 : SectionsForceEvenRankFour (Carrier .Fi22))
    (hFi23 : SectionsForceEvenRankFour (Carrier .Fi23))
    (hFi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime))
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) : Sec6EightMultipliers := by
  intro H _ _ he K p hp hp3 hK hcat hpZ
  have : Group.IsPerfect ↥K := hK.1
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ (alternating_center_small_primes hm e hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    have hdvd := card_center_dvd_of_model hGA hK hmod
    rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
    · exact (sec68_psl he hp hp3 hpZ hmod hpn hpq).elim
    · obtain ⟨rfl, rfl, rfl⟩ := sec68_psu he hp hp3 hpZ hmod hpn hpq
      have hf : 1 ≤ f := hmod.1.2.1
      have hord : (genericOrders .PSU 5 2 f).1 * (genericOrders .PSU 5 2 f).2 *
          ((exceptionalOrders .PSU 5 2 f).1 * (exceptionalOrders .PSU 5 2 f).2) = 5 := by
        have h1 : genericOrders .PSU 5 2 f = (Nat.gcd 5 (2 ^ f + 1), 1) := rfl
        have h2 : exceptionalOrders .PSU 5 2 f = (1, 1) := by
          unfold exceptionalOrders
          simp
        rw [h1, h2, Nat.gcd_eq_left hpq]
        norm_num
      rw [hord] at hdvd
      exact ⟨rfl, Nat.dvd_antisymm hdvd hpZ, f, hf, hmod⟩
  · exact absurd hpZ (exceptionalCenterSmallPrimes_of_griess hGA ↥K hK hex p hp hp3)
  · exfalso
    obtain ⟨s, ⟨e⟩⟩ := hsp
    by_cases hexc : SectionExcluded s
    · have hrank : 4 ≤ evenRank H := by
        rcases hexc with rfl | rfl | rfl | rfl | rfl
        · exact hFi22 H K (center ↥K) ⟨e⟩
        · exact hFi23 H K (center ↥K) ⟨e⟩
        · exact hFi24 H K (center ↥K) ⟨e⟩
        · exact hB H K (center ↥K) ⟨e⟩
        · have : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.1
          exact hM H K (center ↥K) (↥K ⧸ center ↥K) hK.2.2 ⟨MulEquiv.refl _⟩ ⟨e⟩
      have := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank H
      omega
    · obtain ⟨hpair, hnot⟩ := sporadic_residual_of_center e hp hp3 hpZ
      exact hnot (hres.trivial_of_pair hexc hpair)

end CFSG.RankThree.PartOne.Mult
