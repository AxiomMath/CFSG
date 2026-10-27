module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem uc22p22y_exists_fixed_index_le {P Ω K : Type} [Group P] [Finite P] [Group K] [Finite Ω] [Nonempty Ω]
    [MulAction K Ω] {p : ℕ} (hp : p.Prime) (hexp : ∀ x : P, x ^ p = 1)
    (hPab : ∀ x y : P, x * y = y * x) (φ : P →* K) (Inn : Subgroup K)
    (hcyc : IsCyclic ↥(φ.range ⊓ Inn))
    (hquot : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x ∉ Inn → ∃ k : ℕ, x ^ k * y ∈ Inn)
    (hfix : ∀ z ∈ φ.range, z ∉ Inn → ∃ ω : Ω, z • ω = ω) :
    ∃ ω : Ω, ((MulAction.stabilizer K ω).comap φ).index ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hcyc
  have hRp : ∀ x ∈ φ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, hexp, map_one]
  have hRc : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hPab]
  haveI : Finite ↥φ.range :=
    Finite.of_surjective (fun y : P => (⟨φ y, y, rfl⟩ : ↥φ.range)) (fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩)
  have hC : Nat.card ↥(φ.range ⊓ Inn) ≤ p := by
    have h1 : Monoid.exponent ↥(φ.range ⊓ Inn) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => Subtype.ext (hRp x.1 x.2.1))
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos h1
  by_cases h : ∀ y : P, φ y ∈ Inn
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    refine ⟨ω, ?_⟩
    rw [Subgroup.index_comap]
    have hRC : φ.range ⊓ Inn = φ.range := inf_eq_left.2 (by rintro _ ⟨y, rfl⟩; exact h y)
    rw [hRC] at hC
    exact (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans hC
  · push Not at h
    obtain ⟨x₀, hx₀⟩ := h
    have hz : φ x₀ ∈ φ.range := ⟨x₀, rfl⟩
    obtain ⟨ω, hω⟩ := hfix (φ x₀) hz hx₀
    refine ⟨ω, ?_⟩
    rw [Subgroup.index_comap]
    set Sω : Subgroup ↥φ.range := (MulAction.stabilizer K ω).subgroupOf φ.range with hSω
    have hzS : (⟨φ x₀, hz⟩ : ↥φ.range) ∈ Sω := hω
    have hzne : (φ x₀) ≠ 1 := fun h1 => hx₀ (h1 ▸ Inn.one_mem)
    have hord : orderOf (⟨φ x₀, hz⟩ : ↥φ.range) = p := by
      refine orderOf_eq_prime (Subtype.ext (hRp _ hz)) (fun h1 => hzne (congrArg Subtype.val h1))
    have hSp : p ≤ Nat.card ↥Sω := by
      have := Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hzS)
      rwa [Nat.card_zpowers, hord] at this
    have hwz : (φ x₀)⁻¹ ∈ φ.range := φ.range.inv_mem hz
    have hsurj : Function.Surjective (fun q : Fin p × ↥(φ.range ⊓ Inn) =>
        (⟨((φ x₀)⁻¹) ^ (q.1 : ℕ) * (q.2 : K), φ.range.mul_mem (φ.range.pow_mem hwz _) q.2.2.1⟩ :
          ↥φ.range)) := by
      rintro ⟨y, hy⟩
      obtain ⟨k, hk⟩ := hquot (φ x₀) hz y hy hx₀
      have hkc : (φ x₀) ^ k * y ∈ φ.range ⊓ Inn := ⟨φ.range.mul_mem (φ.range.pow_mem hz _) hy, hk⟩
      refine ⟨(⟨k % p, Nat.mod_lt _ hp.pos⟩, ⟨_, hkc⟩), Subtype.ext ?_⟩
      have hwp : ((φ x₀)⁻¹) ^ p = 1 := by rw [inv_pow, hRp _ hz, inv_one]
      show ((φ x₀)⁻¹) ^ (k % p) * ((φ x₀) ^ k * y) = y
      rw [← pow_eq_pow_mod k hwp, inv_pow, inv_mul_cancel_left]
    have hRle : Nat.card ↥φ.range ≤ p * p := by
      haveI : Finite ↥(φ.range ⊓ Inn) :=
        Finite.of_injective (Subgroup.inclusion (inf_le_left : φ.range ⊓ Inn ≤ φ.range))
          (Subgroup.inclusion_injective _)
      have h1 := Nat.card_le_card_of_surjective _ hsurj
      have hfin : Nat.card (Fin p) = p := by simp
      rw [Nat.card_prod, hfin] at h1
      exact h1.trans (Nat.mul_le_mul_left p hC)
    have hmul := Subgroup.card_mul_index Sω
    have h3 : Nat.card ↥Sω * Sω.index ≤ p * p := hmul.le.trans hRle
    have h4 : p * Sω.index ≤ p * p := (Nat.mul_le_mul_right _ hSp).trans h3
    exact Nat.le_of_mul_le_mul_left h4 hp.pos

end CFSG.LocalAnalysis.UniquenessCase.UC22
