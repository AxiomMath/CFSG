module

public import CFSG.GH74.Uniqueness.Bender.Suzuki
public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

variable {K : Type*} [Group K] {q i e : ℕ} {P : Subgroup K} {t : K}

theorem BenderCore.rootCenter_le_of_normal [Finite K] (h : BenderCore q i e P t)
    (hP : IsPGroup 2 P) {N : Subgroup K} (hNP : N ≤ P)
    (hN : ∀ x ∈ P, ∀ y ∈ N, x * y * x⁻¹ ∈ N)
    (hD : ∀ d ∈ cartan P t, ∀ y ∈ N, d * y * d⁻¹ ∈ N) (hne : N ≠ ⊥) : rootCenter P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnorm : (N.subgroupOf P).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hN g g.2 a ha
  have hne' : N.subgroupOf P ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hNP hy⟩ : ↥P) ∈ N.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]; exact hy
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val this
  obtain ⟨z, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hzN : (z : ↥P) ∈ N.subgroupOf P := (Subgroup.mem_inf.mp z.2).1
  have hzC : (z : ↥P) ∈ center ↥P := (Subgroup.mem_inf.mp z.2).2
  have hzZ : ((z : ↥P) : K) ∈ rootCenter P := by
    refine Subgroup.mem_inf.mpr ⟨(z : ↥P).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := (Subgroup.mem_center_iff.mp hzC) ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hz1' : ((z : ↥P) : K) ≠ 1 := by
    intro h1
    apply hz1
    ext
    simpa using h1
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]; exact N.one_mem
  obtain ⟨d, hd, rfl⟩ := h.exists_cartan_conj hzZ hz1' hw hw1
  have := hD d⁻¹ ((cartan P t).inv_mem hd) _ hzN
  simpa using this

theorem BenderType.normal_trichotomy [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (Q : Sylow 2 K) {t : K}
    (hc : BenderCore (2 ^ n) i e (Q : Subgroup K) t) {N : Subgroup K} (hNP : N ≤ Q)
    (hN : ∀ x ∈ (Q : Subgroup K), ∀ y ∈ N, x * y * x⁻¹ ∈ N)
    (hD : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ y ∈ N, d * y * d⁻¹ ∈ N) :
    N = ⊥ ∨ N = rootCenter (Q : Subgroup K) ∨ N = Q := by
  by_cases hne : N = ⊥
  · exact Or.inl hne
  right
  have hZN := hc.rootCenter_le_of_normal Q.isPGroup' hNP hN hD hne
  rcases h.cases' with ⟨hi, -, -⟩ | ⟨hi, he, -⟩ | ⟨hi, -, -⟩
  · subst hi
    right
    have hZQ : rootCenter (Q : Subgroup K) = Q := by
      apply Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      rw [hc.card_center, hc.card_eq, pow_one]
    exact le_antisymm hNP (hZQ ▸ hZN)
  · subst hi
    subst he
    exact hc.suzuki_irreducible (h.suzuki_rootData Q) hZN hNP hD
  · subst hi
    exact h.irreducible_unitary Q hc.sq_eq_one hc.not_mem N hZN hNP hD

end CFSG.GH74.Uniqueness.Bender

end
