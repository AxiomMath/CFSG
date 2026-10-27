module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace ElevenFourteen

theorem index_inf_centralizer_dvd_factorial {V P : Subgroup G}
    (hPV : P ≤ normalizer (V : Set G)) :
    ((P ⊓ centralizer (V : Set G)).subgroupOf P).index ∣ (Nat.card V).factorial := by
  let ψ : ↥P →* Equiv.Perm V :=
    (MulAut.toPerm V).comp (V.normalizerMonoidHom.comp (Subgroup.inclusion hPV))
  have hker : ψ.ker = (P ⊓ centralizer (V : Set G)).subgroupOf P := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, fun v hv => ?_⟩
      have h1 := congrArg (fun σ : Equiv.Perm V => ((σ ⟨v, hv⟩ : V) : G)) h
      have h2 : (x : G) * v * (x : G)⁻¹ = v := h1
      calc v * (x : G) = ((x : G) * v * (x : G)⁻¹) * (x : G) := by rw [h2]
        _ = (x : G) * v := by group
    · rintro ⟨-, h⟩
      refine Equiv.ext fun ⟨v, hv⟩ => Subtype.ext ?_
      have h1 : v * (x : G) = (x : G) * v := h v hv
      show (x : G) * v * (x : G)⁻¹ = v
      calc (x : G) * v * (x : G)⁻¹ = v * (x : G) * (x : G)⁻¹ := by rw [h1]
        _ = v := by group
  rw [← hker, Subgroup.index_ker]
  calc Nat.card ψ.range ∣ Nat.card (Equiv.Perm V) := Subgroup.card_subgroup_dvd_card _
    _ = (Nat.card V).factorial := Nat.card_perm

theorem isCyclic_quotient_of_card_le_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P V₀ : Subgroup G} (hP : IsPGroup p P) (hPV₀ : P ≤ normalizer (V₀ : Set G))
    (hV₀ : Nat.card V₀ ≤ 4)
    [((P ⊓ centralizer (V₀ : Set G)).subgroupOf P).Normal] :
    IsCyclic (↥P ⧸ (P ⊓ centralizer (V₀ : Set G)).subgroupOf P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : Nat.card (↥P ⧸ (P ⊓ centralizer (V₀ : Set G)).subgroupOf P) ∣ 24 := by
    have h1 := index_inf_centralizer_dvd_factorial hPV₀
    have h2 : (Nat.card V₀).factorial ∣ (4 : ℕ).factorial := Nat.factorial_dvd_factorial hV₀
    exact (h1.trans h2 : _ ∣ (4 : ℕ).factorial)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1
    (hP.to_quotient ((P ⊓ centralizer (V₀ : Set G)).subgroupOf P))
  rw [hk] at hdvd
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hcop : Nat.Coprime (p ^ k) 8 := by
    have h8 : Nat.Coprime p (2 ^ 3) := hcop2.pow_right 3
    exact h8.pow_left k
  have h3 : p ^ k ∣ 3 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd : p ^ k ∣ 3 * 8)
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · have hc : Nat.card (↥P ⧸ (P ⊓ centralizer (V₀ : Set G)).subgroupOf P) = 1 := by
      rw [hk, h]
    haveI := (Nat.card_eq_one_iff_unique.1 hc).1
    exact isCyclic_of_subsingleton
  · have hc : Nat.card (↥P ⧸ (P ⊓ centralizer (V₀ : Set G)).subgroupOf P) = 3 := by
      rw [hk, h]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hc

end ElevenFourteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
