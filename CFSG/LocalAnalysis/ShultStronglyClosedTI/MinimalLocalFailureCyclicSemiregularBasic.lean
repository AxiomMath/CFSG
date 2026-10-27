module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G]

theorem fixed_set_eq_pointFixedSet_zpowers (H : Subgroup G) (x : G) :
    {omega : rightCosetSpace H | rightCosetTranslate H omega x = omega} =
      pointFixedSet H (Subgroup.zpowers x) := by
  ext omega
  rw [Set.mem_ofPred_eq, mem_pointFixedSet_iff, Subgroup.zpowers_le,
    mem_rightCosetStabilizer_iff]

theorem mem_normalizer_zpowers_of_inv {t x : G} (htt : t * t = 1)
    (hinv : t⁻¹ * x * t = x⁻¹) : t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconj : t * x * t⁻¹ = x⁻¹ := by
    rw [htinv]
    rw [htinv] at hinv
    exact hinv
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← conj_zpow, hconj, inv_zpow']
    exact Subgroup.zpow_mem_zpowers x (-k)
  · intro hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hgk : g = t * x ^ k * t⁻¹ :=
      calc g = t⁻¹ * (t * g * t⁻¹) * t := by group
        _ = t * x ^ k * t⁻¹ := by rw [← hk, htinv]
    rw [hgk, ← conj_zpow, hconj, inv_zpow']
    exact Subgroup.zpow_mem_zpowers x (-k)

theorem mem_centralizer_zpowers_of_commute {x c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) :
    c ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcx : Commute x c := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  exact (hcx.zpow_left k).eq

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
