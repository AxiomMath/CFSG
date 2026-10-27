module

public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviCycData

public section

open scoped IsMulCommutative

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem e6Levi_card_le_three_of_fixedBy {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [Finite X] (hexp : ∀ g : G, g ^ 3 = 1) (hX : Nat.card X = 72)
    (hfix : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = 12) : Nat.card G ≤ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 G := fun g => ⟨1, by simpa using hexp g⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  by_contra hlt
  push Not at hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> simp at hk <;> omega
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  haveI : ∀ g : G, Fintype (MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hcardG : Fintype.card G = 3 ^ k := by rw [← Nat.card_eq_fintype_card, hk]
  have hsum : ∑ g : G, Fintype.card (MulAction.fixedBy X g) = 72 + 12 * (3 ^ k - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    have h1 : Fintype.card (MulAction.fixedBy X (1 : G)) = 72 := by
      rw [← Nat.card_eq_fintype_card, ← hX]
      have e : MulAction.fixedBy X (1 : G) = Set.univ := by
        ext x
        simp [MulAction.mem_fixedBy]
      rw [e]
      exact Nat.card_congr (Equiv.Set.univ X)
    have h2 : ∀ g ∈ Finset.univ.erase (1 : G), Fintype.card (MulAction.fixedBy X g) = 12 := by
      intro g hg
      rw [← Nat.card_eq_fintype_card]
      exact hfix g (Finset.ne_of_mem_erase hg)
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, hcardG, smul_eq_mul, mul_comm]
  rw [hsum, hcardG] at hB
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 9 * m := ⟨3 ^ (k - 2), by
    rw [show 9 = 3 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
  have hpos : 0 < 3 ^ k := by positivity
  rw [hm] at hB hpos
  have : 9 ∣ 72 + 12 * (9 * m - 1) := by
    rw [hB]
    exact Dvd.intro (Fintype.card (Quotient (MulAction.orbitRel G X)) * m) (by ring)
  omega


theorem e6Levi_pow_three_comm_mem_zpowers {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha : ∀ i, a i ^ 3 = 1) (hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 24, 40} : Set ℕ))
    {w₁ w₂ : WeylGroup Tag.E6} (h₁ : w₁ ∈ kernelReflectionGroup a)
    (h₂ : w₂ ∈ kernelReflectionGroup a) (h₁3 : w₁ ^ 3 = 1) (h₂3 : w₂ ^ 3 = 1)
    (hc : w₁ * w₂ = w₂ * w₁) : w₁ = 1 ∨ w₂ ∈ Subgroup.zpowers w₁ := by
  classical
  by_cases hw1 : w₁ = 1
  · exact Or.inl hw1
  refine Or.inr ?_
  have hcomm : ({w₁, w₂} : Set (WeylGroup Tag.E6)).Pairwise Commute := by
    intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hc
    · exact hc.symm
    · exact absurd rfl hxy
  haveI : IsMulCommutative (Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6))) :=
    Subgroup.isMulCommutative_closure hcomm
  have hcommU : ∀ x ∈ Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6)),
      ∀ y ∈ Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6)), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Subgroup.closure
      ({w₁, w₂} : Set (WeylGroup Tag.E6))) ⟨y, hy⟩)
  have hexp : ∀ g ∈ Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6)), g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact h₁3
      · exact h₂3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      rw [Commute.mul_pow (hcommU x hx y hy) 3, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hle : Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6)) ≤ kernelReflectionGroup a := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  have hcard : Nat.card (Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6))) ≤ 3 := by
    refine e6Levi_card_le_three_of_fixedBy
      (X := {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) (fun g => Subtype.ext (hexp g g.2))
      e6_nat_card_roots fun g hg => ?_
    have hg1 : (g : WeylGroup Tag.E6) ≠ 1 := fun h => hg (Subtype.ext h)
    obtain ⟨α, β, hab, hgeq⟩ :=
      e6Levi_eq_pairRefl_of_pow_three a ha hk (hle g.2) (hexp g g.2) hg1
    have h12 := e6_card_fixedBy_pairRefl hab
    rw [← hgeq] at h12
    exact h12
  have hord : orderOf w₁ = 3 := orderOf_eq_prime h₁3 hw1
  have hz : Subgroup.zpowers w₁ ≤ Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6)) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hzcard : Nat.card (Subgroup.zpowers w₁) = 3 := by rw [Nat.card_zpowers, hord]
  have hUeq : Subgroup.zpowers w₁ = Subgroup.closure ({w₁, w₂} : Set (WeylGroup Tag.E6)) :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [hzcard]; exact hcard)
  rw [hUeq]
  exact Subgroup.subset_closure (by simp)

end CFSG.StandardType.SCFourCover

end
