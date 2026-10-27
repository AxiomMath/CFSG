module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Mathlib.GroupTheory.CyclicPowers

public section

namespace IsCyclic

private theorem cq1_three_dvd_card_of_nonCube {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {c : G} (hc : ∀ x : G, x ^ 3 ≠ c) : 3 ∣ Nat.card G := by
  by_contra h
  have hcop : (Nat.card G).Coprime 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr h).symm
  obtain ⟨x, hx⟩ := hcop.pow_left_bijective.surjective c
  exact hc x hx

theorem exists_pow_mul_cube {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {c : G}
    (hc : ∀ x : G, x ^ 3 ≠ c) (a : G) : ∃ (j : ℕ) (l : G), j < 3 ∧ a = c ^ j * l ^ 3 := by
  classical
  have h3 : 3 ∣ Nat.card G := cq1_three_dvd_card_of_nonCube hc
  have hN : Nat.card G / 3 * 3 = Nat.card G := Nat.div_mul_cancel h3
  let e : G := c ^ (Nat.card G / 3)
  have he3 : e ^ 3 = 1 := by
    dsimp only [e]
    rw [← pow_mul, hN, pow_card_eq_one']
  have hene : c ^ (Nat.card G / 3) ≠ 1 := by
    intro he
    obtain ⟨v, hv⟩ := exists_pow_eq_of_pow_card_div_eq_one (n := 3) (by norm_num) h3 he
    exact hc v hv
  have horde : orderOf e = 3 := orderOf_eq_prime he3 hene
  have hker : Nat.card (powMonoidHom 3 : G →* G).ker = 3 := by
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_eq_right h3
  have hle : Subgroup.zpowers e ≤ (powMonoidHom 3 : G →* G).ker := by
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr (by simpa using he3)
  have hEq : Subgroup.zpowers e = (powMonoidHom 3 : G →* G).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hker, Nat.card_zpowers, horde])
  have hd3 : (a ^ (Nat.card G / 3)) ^ 3 = 1 := by
    rw [← pow_mul, hN, pow_card_eq_one']
  have hdmem : a ^ (Nat.card G / 3) ∈ Subgroup.zpowers e := by
    rw [hEq]
    exact MonoidHom.mem_ker.mpr (by simpa using hd3)
  rw [mem_zpowers_iff_mem_range_orderOf] at hdmem
  obtain ⟨j, hjmem, hjd⟩ := Finset.mem_image.mp hdmem
  rw [Finset.mem_range, horde] at hjmem
  have hd : (c ^ j) ^ (Nat.card G / 3) = a ^ (Nat.card G / 3) := by
    rw [← hjd]
    dsimp only [e]
    calc (c ^ j) ^ (Nat.card G / 3)
        = c ^ (j * (Nat.card G / 3)) := (pow_mul c j (Nat.card G / 3)).symm
      _ = c ^ ((Nat.card G / 3) * j) := by rw [mul_comm]
      _ = (c ^ (Nat.card G / 3)) ^ j := pow_mul c (Nat.card G / 3) j
  have hu : (a * (c ^ j)⁻¹) ^ (Nat.card G / 3) = 1 := by
    rw [mul_pow, inv_pow, hd, mul_inv_cancel]
  obtain ⟨l, hl⟩ := exists_pow_eq_of_pow_card_div_eq_one (n := 3) (by norm_num) h3 hu
  refine ⟨j, l, hjmem, ?_⟩
  rw [hl, ← mul_assoc, mul_comm (c ^ j) a, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_pow_three_eq_one_ne_one {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {c : G}
    (hc : ∀ x : G, x ^ 3 ≠ c) : ∃ ω : G, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have h3 : 3 ∣ Nat.card G := cq1_three_dvd_card_of_nonCube hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g ^ (Nat.card G / 3), ?_, ?_⟩
  · rw [← pow_mul, Nat.div_mul_cancel h3, pow_card_eq_one']
  · intro h1
    have hdvd : orderOf g ∣ Nat.card G / 3 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have hle : Nat.card G ≤ Nat.card G / 3 :=
      Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd Nat.card_pos h3) (by norm_num)) hdvd
    exact absurd hle (not_le.mpr (Nat.div_lt_self Nat.card_pos (by norm_num)))

end IsCyclic
