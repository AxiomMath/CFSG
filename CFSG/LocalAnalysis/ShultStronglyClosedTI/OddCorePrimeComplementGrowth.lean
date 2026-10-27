module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthSylow
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

theorem odd_core_normalizer_generation_strict_prime_complement_growth
    (J : Subgroup G) (hJ : J ≠ ⊥) (hJodd : Odd (Nat.card J))
    (hcorefree : ∀ N : Subgroup G, N.Normal → N ≤ J → N = ⊥)
    (z : G) (hz : orderOf z = 2)
    (hgen : Subgroup.closure ((Subgroup.normalizer (J : Set G) : Set G) ∪ {z}) = ⊤)
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (V : Subgroup G) (hVJ : V ≤ J) (hVz : conjugate V z = V)
    (hpart : CFSG.OrderReductions.PrimePart.primePart p (Nat.card V) =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card J)) :
    (piCore {q : Nat.Primes | q.val ≠ p} V).map V.subtype <
        (piCore {q : Nat.Primes | q.val ≠ p} J).map J.subtype ∧
      (piCore {q : Nat.Primes | q.val ≠ p} J).map J.subtype ≠ ⊥ := by
  let : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard J hJodd
  let : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ
  have hle := primeComplementGrowth_full_prime_part_core_le p V J hVJ hpart
  have hne : (piCore {q : Nat.Primes | q.val ≠ p} V).map V.subtype ≠
      (piCore {q : Nat.Primes | q.val ≠ p} J).map J.subtype := by
    intro heq
    have hnormV := primeComplementGrowth_mem_normalizer_of_conjugate_eq V z hVz
    have hnormR : z ∈ Subgroup.normalizer
        (CFSG.OrderReductions.PrimeComplementCore.ambientCore p J : Set G) := by
      rw [primeComplementGrowth_native_ambient_core_eq, ← heq,
        ← primeComplementGrowth_native_ambient_core_eq]
      exact CFSG.OrderReductions.RegularCore.characteristic_pair_image_normalizes V
        (CFSG.OrderReductions.PrimeComplementCore.primeComplementCore p V) z hnormV
    obtain ⟨P, _, hnormP⟩ :=
      primeComplementGrowth_exists_invariant_sylow p V J hVJ hJodd z hz hVz hpart
    let A : Subgroup J := CFSG.OrderReductions.ThompsonCoreProduct.coreProduct p P
    have hAchar : A.Characteristic :=
      CFSG.OrderReductions.ThompsonSolvableOdd.coreProduct_characteristic_of_solvable_odd
        p hpodd hJodd P
    let : A.Characteristic := hAchar
    have hzA : z ∈ Subgroup.normalizer (A.map J.subtype : Set G) :=
      CFSG.OrderReductions.ThompsonNormalizer.coreProduct_image_normalizes p J P z
        hnormR hnormP
    have hAnormal : (A.map J.subtype).Normal :=
      primeComplementGrowth_normal_of_normalizer_generation J (A.map J.subtype) z hgen
        (primeComplementGrowth_normalizer_le_characteristic_image_normalizer J A) hzA
    have hAbot : A.map J.subtype = ⊥ :=
      hcorefree (A.map J.subtype) hAnormal (Subgroup.map_subtype_le A)
    have hAone : A = ⊥ := by
      apply Subgroup.map_injective (f := J.subtype) Subtype.val_injective
      simpa only [Subgroup.map_bot] using hAbot
    exact CFSG.OrderReductions.ThompsonCoreProduct.coreProduct_nontrivial p P hAone
  have hstrict := lt_of_le_of_ne hle hne
  refine ⟨hstrict, ?_⟩
  intro hbot
  rw [hbot] at hstrict
  exact not_lt_bot hstrict

theorem odd_core_normalizer_generation_strict_pPrimeCore_growth
    (J : Subgroup G) (hJ : J ≠ ⊥) (hJodd : Odd (Nat.card J))
    (hcorefree : ∀ N : Subgroup G, N.Normal → N ≤ J → N = ⊥)
    (z : G) (hz : orderOf z = 2)
    (hgen : Subgroup.closure ((Subgroup.normalizer (J : Set G) : Set G) ∪ {z}) = ⊤)
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (V : Subgroup G) (hVJ : V ≤ J) (hVz : conjugate V z = V)
    (hpart : CFSG.OrderReductions.PrimePart.primePart p (Nat.card V) =
      CFSG.OrderReductions.PrimePart.primePart p (Nat.card J)) :
    (pPrimeCore p V).map V.subtype < (pPrimeCore p J).map J.subtype ∧
      (pPrimeCore p J).map J.subtype ≠ ⊥ := by
  simpa only [pPrimeCore_eq_piCore] using
    odd_core_normalizer_generation_strict_prime_complement_growth
      J hJ hJodd hcorefree z hz hgen p hpodd V hVJ hVz hpart

end CFSG.ShultStronglyClosedTI
