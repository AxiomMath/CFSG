module

public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks
public import CFSG.RankThree.PartOne.S15K.PiGLDecomp
import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Matrix CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open scoped _root_.Classical

variable {K : Type} [Field K] {n : ℕ} {x : Module.End K (Fin n → K)}

theorem primaryMultiplicity_le_finrank {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {y : Module.End K V} (hy : Squarefree (minpoly K y))
    (c : primaryFactors y) : primaryMultiplicity y (c : K[X]) ≤ Module.finrank K V := by
  rw [finrank_eq_sum_degree_mul_multiplicity hy]
  have hdeg : 1 ≤ (c : K[X]).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.2
      (Polynomial.degree_pos_of_irreducible (irreducible_of_mem_primaryFactors c.2))
  calc primaryMultiplicity y (c : K[X])
      ≤ (c : K[X]).natDegree * primaryMultiplicity y (c : K[X]) := Nat.le_mul_of_pos_left _ hdeg
    _ ≤ ∑ a : primaryFactors y, (a : K[X]).natDegree * primaryMultiplicity y (a : K[X]) :=
        Finset.single_le_sum
          (f := fun a : primaryFactors y => (a : K[X]).natDegree * primaryMultiplicity y (a : K[X]))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem exists_block_decomp {p : ℕ} (hp : p.Prime) (hsq : Squarefree (minpoly K x))
    (c : primaryFactors x) (hmult : ¬ p ∣ mult x c) {g : GL (Fin n) K}
    (hg : g ∈ (commutantUnitsToGL x).range) (hgp : g ^ p = 1) :
    ∃ X ∈ blockImage hsq c, ∀ f ∈ blockImage hsq c, (X⁻¹ * g) * f = f * (X⁻¹ * g) := by
  rw [← range_blockTheta hsq] at hg
  obtain ⟨w, rfl⟩ := hg
  have hwp : w ^ p = 1 := blockTheta_injective hsq (by rw [map_pow, hgp, map_one])
  obtain ⟨s, hs⟩ := exists_blockEmbed_decomp hp w hwp c hmult
  refine ⟨blockTheta hsq (blockEmbed (Efac x) (mult x) c s), mem_blockImage.2 ⟨s, rfl⟩, fun f hf => ?_⟩
  obtain ⟨s', rfl⟩ := mem_blockImage.1 hf
  have h1 : (blockTheta hsq (blockEmbed (Efac x) (mult x) c s))⁻¹ * blockTheta hsq w =
      blockTheta hsq ((blockEmbed (Efac x) (mult x) c s)⁻¹ * w) := by rw [map_mul, map_inv]
  rw [h1, ← map_mul, ← map_mul, hs s']

theorem eq_one_of_central_pow_of_card {F : Type*} [Field F] [Finite F] {m p : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hmp : ¬ p ∣ m) (s : SpecialLinearGroup (Fin m) F)
    (hcomm : ∀ s' : SpecialLinearGroup (Fin m) F, s * s' = s' * s) (hsp : s ^ p = 1) : s = 1 := by
  have hscen : s ∈ Subgroup.center (SpecialLinearGroup (Fin m) F) :=
    Subgroup.mem_center_iff.2 fun s' => (hcomm s').symm
  have hcard := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := m) hm F
  have hord : orderOf s ∣ m := by
    have h1 := orderOf_dvd_natCard (⟨s, hscen⟩ : Subgroup.center (SpecialLinearGroup (Fin m) F))
    rw [Subgroup.orderOf_mk] at h1
    exact h1.trans (hcard.trans (Nat.gcd_dvd_left _ _))
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hsp) with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd (h1 ▸ hord) hmp

theorem block_center_pow [Finite K] {p : ℕ} (hp : p.Prime) (hsq : Squarefree (minpoly K x))
    (c : primaryFactors x) (hc : 2 ≤ mult x c) (hmult : ¬ p ∣ mult x c) :
    ∀ u ∈ blockImage hsq c, (∀ f ∈ blockImage hsq c, u * f = f * u) → u ^ p = 1 → u = 1 := by
  intro u hu hcen hup
  obtain ⟨s, hs⟩ := mem_blockImage.1 hu
  have : Module.Finite K (Efac x c) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible (c : K[X])).ne_zero).finite
  have : Finite (Efac x c) := Module.finite_of_finite K
  have hm1 : 1 ≤ mult x c := by omega
  have hs1 : s = 1 := by
    refine eq_one_of_central_pow_of_card hm1 hp hmult s ?_ ?_
    · intro s'
      have h1 := hcen (blockTheta hsq (blockEmbed (Efac x) (mult x) c s'))
        (mem_blockImage.2 ⟨s', rfl⟩)
      rw [← hs] at h1
      have h2 : blockEmbed (Efac x) (mult x) c s * blockEmbed (Efac x) (mult x) c s' =
          blockEmbed (Efac x) (mult x) c s' * blockEmbed (Efac x) (mult x) c s := by
        apply blockTheta_injective hsq
        rw [map_mul, map_mul]
        exact h1
      refine blockEmbed_injective c ?_
      rw [map_mul, map_mul]
      exact h2
    · refine blockEmbed_injective c (blockTheta_injective hsq ?_)
      rw [map_pow, map_pow, hs, hup, map_one, map_one]
  rw [← hs, hs1, map_one, map_one]

end CFSG.RankThree.PartOne.S15K
