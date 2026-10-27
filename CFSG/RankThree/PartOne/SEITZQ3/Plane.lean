module

public import CFSG.RankThree.PartOne.SEITZQ1.Plane

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ3

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.SEITZQ1

variable {f : ℕ} {K' : Type} [Field K']

theorem q3_plane (h : UnitaryFieldData 2 f K') (hpq : 3 ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (unitarySU 2 f K' 3),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 3 ^ 2 ∧
      (∀ x ∈ E, ∀ i j : Fin 3, i ≠ j →
        ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0) ∧
      ∃ x₀ ∈ E, x₀ ≠ 1 ∧ ∃ z : K', z ≠ 0 ∧
        ((x₀ : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = Matrix.diagonal ![z, 1, z⁻¹] := by
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card K'ˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [Nat.card_units, h.card, pow_mul']
    exact h1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 (hcard ▸ Dvd.dvd.mul_right hpq _)
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact Nat.prime_three.one_lt.ne hζ
  set S := Subgroup.zpowers ζ with hS
  have hSp : ∀ s ∈ S, s ^ 3 = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]))
  have hSq : ∀ s ∈ S, s ^ (2 ^ f + 1) = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]; exact hpq))
  let E₀ : Subgroup (GL (Fin 3) K') := (S.prod S).map q1DiagTorus
  have hE₀G : E₀ ≤ unitarySU 2 f K' 3 := by
    rintro _ ⟨u, hu, rfl⟩
    exact q1DiagTorus_mem_unitarySU h (Prod.ext (hSq _ hu.1) (hSq _ hu.2))
  refine ⟨E₀.subgroupOf (unitarySU 2 f K' 3), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨v, hv, hyv⟩ := Subgroup.mem_subgroupOf.mp hy
    apply Subtype.ext
    show (x : GL (Fin 3) K') * y = y * x
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, mul_comm u v]
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    have hup : u ^ 3 = 1 := Prod.ext (hSp _ hu.1) (hSp _ hu.2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hxu, ← map_pow, hup, map_one]
    rfl
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀G).toEquiv,
      Subgroup.card_map_of_injective q1DiagTorus_injective,
      Nat.card_congr (Subgroup.prodEquiv S S).toEquiv, Nat.card_prod, hS, Nat.card_zpowers, hζ,
      sq]
  · intro x hx i j hij
    obtain ⟨u, hu, hxu⟩ := Subgroup.mem_subgroupOf.mp hx
    rw [← hxu, coe_q1DiagTorus]
    exact Matrix.diagonal_apply_ne _ hij
  · have hζS : ζ ∈ S := Subgroup.mem_zpowers ζ
    refine ⟨⟨q1DiagTorus (ζ, ζ), hE₀G ⟨(ζ, ζ), ⟨hζS, hζS⟩, rfl⟩⟩,
      Subgroup.mem_subgroupOf.mpr ⟨(ζ, ζ), ⟨hζS, hζS⟩, rfl⟩, ?_, (ζ : K'), ζ.ne_zero, ?_⟩
    · intro h1
      have h2 : q1DiagTorus (ζ, ζ) = q1DiagTorus 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact hζ1 (congrArg Prod.fst (q1DiagTorus_injective h2))
    · show (q1DiagTorus (ζ, ζ) : Matrix (Fin 3) (Fin 3) K') = _
      rw [coe_q1DiagTorus]
      congr 1
      funext i
      fin_cases i <;> simp

end CFSG.RankThree.PartOne.SEITZQ3
