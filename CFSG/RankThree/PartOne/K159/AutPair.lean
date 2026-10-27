module

public import CFSG.RankThree.PartOne.K159.AutCore

public section

namespace CFSG.RankThree.PartOne.K159

variable {G : Type*} [Group G]

@[expose] def pairSub (p : ℕ) (hp : 0 < p) (a b : G) (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {x | ∃ i j : ℕ, x = a ^ i * b ^ j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    have hc : Commute (b ^ j) (a ^ k) :=
      Commute.pow_pow (show Commute b a from hab.symm) j k
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc.eq]
      _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨(p - 1) * i, (p - 1) * j, ?_⟩
    have hc : Commute (b ^ ((p - 1) * j)) (a ^ i) :=
      Commute.pow_pow (show Commute b a from hab.symm) _ _
    have h1 : a ^ ((p - 1) * i) * b ^ ((p - 1) * j) * (a ^ i * b ^ j) = 1 := by
      calc a ^ ((p - 1) * i) * b ^ ((p - 1) * j) * (a ^ i * b ^ j)
          = a ^ ((p - 1) * i) * (b ^ ((p - 1) * j) * a ^ i) * b ^ j := by simp only [mul_assoc]
        _ = a ^ ((p - 1) * i) * (a ^ i * b ^ ((p - 1) * j)) * b ^ j := by rw [hc.eq]
        _ = a ^ ((p - 1) * i + i) * b ^ ((p - 1) * j + j) := by
          rw [pow_add, pow_add]; simp only [mul_assoc]
        _ = 1 := by
          have e1 : (p - 1) * i + i = p * i := by
            have : (p - 1) * i + i = ((p - 1) + 1) * i := by ring
            rw [this, Nat.sub_add_cancel hp]
          have e2 : (p - 1) * j + j = p * j := by
            have : (p - 1) * j + j = ((p - 1) + 1) * j := by ring
            rw [this, Nat.sub_add_cancel hp]
          rw [e1, e2, pow_mul, pow_mul, ha, hb]; simp
    exact (eq_inv_of_mul_eq_one_left h1).symm

theorem autWitness_of_pair [Finite G] {p : ℕ} (hp : p.Prime) (K : Subgroup G) {a b g : G} (haK : a ∈ K)
    (hbK : b ∈ K) (hgK : g ∈ K) (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < p → j < p → i' < p → j' < p →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j')
    (hga : ∃ i j : ℕ, g * a * g⁻¹ = a ^ i * b ^ j) (hgb : ∃ i j : ℕ, g * b * g⁻¹ = a ^ i * b ^ j)
    (hmove : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → g ^ k * a * (g ^ k)⁻¹ ≠ a) :
    AutWitness p ↥K := by
  have hp0 : 0 < p := hp.pos
  set U : Subgroup G := pairSub p hp0 a b ha hb hab with hU
  have hUK : U ≤ K := by
    rintro _ ⟨i, j, rfl⟩
    exact mul_mem (pow_mem haK i) (pow_mem hbK j)
  have haU : a ∈ U := ⟨1, 0, by simp⟩
  have hbU : b ∈ U := ⟨0, 1, by simp⟩
  refine ⟨U.subgroupOf K, ?_, ?_, ⟨g, hgK⟩, ?_, ?_⟩
  · rintro ⟨u, hu⟩ hu'
    obtain ⟨i, j, rfl⟩ := Subgroup.mem_subgroupOf.1 hu'
    apply Subtype.ext
    have hc : Commute (a ^ i) (b ^ j) := Commute.pow_pow hab i j
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i p, mul_comm j p, pow_mul, pow_mul, ha, hb]
    simp
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
    have hinj' : Function.Injective
        (fun x : Fin p × Fin p => (⟨a ^ (x.1 : ℕ) * b ^ (x.2 : ℕ), x.1, x.2, rfl⟩ : U)) := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h' := congrArg Subtype.val h
      obtain ⟨e1, e2⟩ := hinj i j i' j' i.2 j.2 i'.2 j'.2 h'
      simp [Fin.ext e1, Fin.ext e2]
    have := Nat.card_le_card_of_injective _ hinj'
    simpa [Nat.card_eq_fintype_card, sq] using this
  · rintro ⟨u, hu⟩ hu'
    refine Subgroup.mem_subgroupOf.2 ?_
    obtain ⟨i, j, rfl⟩ := Subgroup.mem_subgroupOf.1 hu'
    have hga' : g * a * g⁻¹ ∈ U := by
      obtain ⟨i, j, h⟩ := hga
      exact h ▸ ⟨i, j, rfl⟩
    have hgb' : g * b * g⁻¹ ∈ U := by
      obtain ⟨i, j, h⟩ := hgb
      exact h ▸ ⟨i, j, rfl⟩
    have : g * (a ^ i * b ^ j) * g⁻¹ = (g * a * g⁻¹) ^ i * (g * b * g⁻¹) ^ j := by
      rw [conj_pow, conj_pow]
      group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this]
    exact mul_mem (pow_mem hga' i) (pow_mem hgb' j)
  · intro k hk1 hk4
    refine ⟨⟨a, hUK haU⟩, Subgroup.mem_subgroupOf.2 haU, fun h => ?_⟩
    apply hmove k hk1 hk4
    simpa using congrArg Subtype.val h

end CFSG.RankThree.PartOne.K159
