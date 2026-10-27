module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoGeneral
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped commutatorElement

namespace OuterPrimeTwoSymplectic

theorem commutator_mem_of_cyclic_quotient {Y : Type*} [Group Y] {D E : Subgroup Y}
    [(D.subgroupOf E).Normal] {g : Y} (hg : g ∈ E) (hgen : ∀ z ∈ E, ∃ k : ℤ, g ^ k * z ∈ D)
    {x y : Y} (hx : x ∈ E) (hy : y ∈ E) : ⁅x, y⁆ ∈ D := by
  have hpow : ∀ q : E ⧸ D.subgroupOf E,
      ∃ m : ℤ, (QuotientGroup.mk (⟨g, hg⟩ : E) : E ⧸ D.subgroupOf E) ^ m = q := by
    intro q
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hgen z hz
    refine ⟨-k, ?_⟩
    have h1 : (QuotientGroup.mk (⟨g, hg⟩ : E) : E ⧸ D.subgroupOf E) ^ k *
        (QuotientGroup.mk (⟨z, hz⟩ : E) : E ⧸ D.subgroupOf E) = 1 := by
      rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
        mem_subgroupOf]
      exact hk
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have hcomm : ∀ q₁ q₂ : E ⧸ D.subgroupOf E, q₁ * q₂ = q₂ * q₁ := by
    intro q₁ q₂
    obtain ⟨m, rfl⟩ := hpow q₁
    obtain ⟨n, rfl⟩ := hpow q₂
    exact zpow_mul_comm _ m n
  have h : (QuotientGroup.mk (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : E) :
      E ⧸ D.subgroupOf E) = 1 := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (QuotientGroup.mk (⟨x, hx⟩ : E)) (QuotientGroup.mk (⟨y, hy⟩ : E))]
    group
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h
  rw [commutatorElement_def]
  exact h

variable {r : ℕ} {K : Type} [Field K]

theorem commutator_mem_spLinearAutGroup [Finite K] (hr : 1 ≤ r)
    {x y : MulAut (StatedProj (StatedSp r K))} (hx : x ∈ spSemilinearAutGroup r K)
    (hy : y ∈ spSemilinearAutGroup r K) : ⁅x, y⁆ ∈ spLinearAutGroup r K := by
  obtain ⟨-, -, hnorm, -, ⟨g, hg, hgen⟩, -⟩ := standard_outer_quotient (K := K) hr
  exact commutator_mem_of_cyclic_quotient hg hgen hx hy

theorem normal_spSemilinearAutGroup [Finite K] (hr : 2 ≤ r) :
    (spSemilinearAutGroup r K).Normal := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (index_spSemilinearAutGroup_dvd_two (K := K) hr)
    with h | h
  · exact Subgroup.normal_of_index_eq_one h
  · exact Subgroup.normal_of_index_eq_two h

theorem isCyclic_map_spLinearAutGroup [NeZero r] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) :
    IsCyclic ((spLinearAutGroup r K).map
      (QuotientGroup.mk' (inner (StatedProj (StatedSp r K))))) := by
  have hcard : Nat.card ((spLinearAutGroup r K).map
      (QuotientGroup.mk' (inner (StatedProj (StatedSp r K))))) =
      (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) := by
    rw [← relIndex_bot_left, ← relIndex_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hdvd := (relIndex_inner_spLinearAutGroup_dvd (r := r) hp hf hK).trans
    (Nat.gcd_dvd_left 2 _)
  exact isCyclic_of_card_dvd_prime (p := 2) (by rw [hcard]; exact hdvd)

end OuterPrimeTwoSymplectic

open OuterPrimeTwoSymplectic

theorem outerPrimeTwoTrivial_symplecticProj {n p f : ℕ} {K : Type} [Field K] [Finite K]
    [Finite (StatedProj (StatedSp n K))] (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hn : 2 ≤ n) : OuterPrimeTwoTrivial (StatedProj (StatedSp n K)) := by
  have : NeZero n := ⟨by omega⟩
  set π := QuotientGroup.mk' (inner (StatedProj (StatedSp n K)))
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have : ((spSemilinearAutGroup n K).map π).Normal :=
    (normal_spSemilinearAutGroup (K := K) hn).map π hπs
  have : IsCyclic ((spLinearAutGroup n K).map π) := isCyclic_map_spLinearAutGroup hp hf hK
  refine outerPrimeTwoTrivial_of_two_layer ((spSemilinearAutGroup n K).map π)
    ((spLinearAutGroup n K).map π)
    (Subgroup.map_mono spLinearAutGroup_le_spSemilinearAutGroup) ?_ ?_
  · intro x
    obtain ⟨y, rfl⟩ := hπs x
    exact ⟨y ^ 2, sq_mem_spSemilinearAutGroup hn y, map_pow π y 2⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨⁅x, y⁆, commutator_mem_spLinearAutGroup (by omega) hx hy,
      map_commutatorElement π x y⟩

theorem outerPrimeTwoTrivial_symplectic {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSp n p f) : OuterPrimeTwoTrivial S := by
  obtain ⟨⟨hp, hf, hn, -⟩, K, hKfield, hKfin, hK, ⟨e⟩⟩ := h
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv S e.toEquiv
  exact outerPrimeTwoTrivial_of_mulEquiv e (outerPrimeTwoTrivial_symplecticProj hp hf hK hn)

end CFSG.RankThree.PartOne
