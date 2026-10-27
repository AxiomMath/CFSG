module

public import CFSG.OddTranspositions.PartThree.EightOne.Bender
public import CFSG.OddTranspositions.PartThree.EightOne.Quotient

public section

namespace CFSG.OddTranspositions.PartThree.EightOne

open CFSG.Timmesfeld.Bridge.Asc72

theorem mem_one_two_three_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ∈ ({1, 2, 3} : Set ℕ)) :
    m ∈ ({1, 2, 3} : Set ℕ) := by
  rcases hn with rfl | rfl | rfl
  · simp [Nat.dvd_one.mp hmn]
  · rcases (Nat.dvd_prime Nat.prime_two).mp hmn with rfl | rfl <;> simp
  · rcases (Nat.dvd_prime Nat.prime_three).mp hmn with rfl | rfl <;> simp

theorem not_forall_orderOf_mul_mem {G : Type} [Group G] [Finite G]
    {D : Set G} (hS : Setup G D) {R N : Subgroup G} [R.Normal] [N.Normal] (hNR : N ≤ R)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ R)) :
    ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf ((d : G ⧸ N) * (e : G ⧸ N)) ∈ ({1, 2, 3} : Set ℕ) := by
  intro H
  obtain ⟨d₀, hd₀⟩ := hS.nonempty
  have ha_ne : (d₀ : G ⧸ R) ≠ 1 := fun h1 =>
    not_mem_of_isBenderGroup hS hB hd₀ ((QuotientGroup.eq_one_iff d₀).mp h1)
  have ha_sq : (d₀ : G ⧸ R) ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, hS.oddT.mul_self_eq_one hd₀, QuotientGroup.mk_one]
  have ha : orderOf (d₀ : G ⧸ R) = 2 := orderOf_eq_prime ha_sq ha_ne
  obtain ⟨x, y, hxconj, hyconj, hxy⟩ := exists_isConj_orderOf_mul_not_mem hB ha
  obtain ⟨c, hc⟩ := isConj_iff.mp hxconj
  obtain ⟨c', hc'⟩ := isConj_iff.mp hyconj
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective c'
  have hxval : x = ((g * d₀ * g⁻¹ : G) : G ⧸ R) := by
    rw [← hc]
    simp
  have hyval : y = ((g' * d₀ * g'⁻¹ : G) : G ⧸ R) := by
    rw [← hc']
    simp
  let ρ : G ⧸ N →* G ⧸ R := QuotientGroup.map N R (MonoidHom.id G) (by simpa using hNR)
  have hρ : ∀ z : G, ρ (z : G ⧸ N) = (z : G ⧸ R) := fun z =>
    QuotientGroup.map_mk N R (MonoidHom.id G) (by simpa using hNR) z
  have hmul : x * y =
      ρ (((g * d₀ * g⁻¹ : G) : G ⧸ N) * ((g' * d₀ * g'⁻¹ : G) : G ⧸ N)) := by
    rw [hxval, hyval, map_mul, hρ, hρ]
  have hdvd : orderOf (x * y) ∣
      orderOf (((g * d₀ * g⁻¹ : G) : G ⧸ N) * ((g' * d₀ * g'⁻¹ : G) : G ⧸ N)) := by
    rw [hmul]
    exact orderOf_map_dvd ρ _
  exact hxy (mem_one_two_three_of_dvd hdvd
    (H (g * d₀ * g⁻¹) (hS.conj_mem g hd₀) (g' * d₀ * g'⁻¹) (hS.conj_mem g' hd₀)))

end CFSG.OddTranspositions.PartThree.EightOne
