module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.A5S5

open Equiv

set_option synthInstance.maxSize 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev Bad (y t : Perm (Fin 5)) : Prop :=
  (t * (y * t * y⁻¹)) ^ 4 ≠ 1 ∨ (t * (y * t * y⁻¹)⁻¹) ^ 4 ≠ 1 ∨
    (t * (y ^ 2 * t * (y ^ 2)⁻¹)) ^ 4 ≠ 1 ∨ (t * (y ^ 2 * t * (y ^ 2)⁻¹)⁻¹) ^ 4 ≠ 1

private def y3 : Perm (Fin 5) := swap 0 1 * swap 1 2

private def y5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

private theorem exists_conj_y3 : ∀ y : Perm (Fin 5), y ≠ 1 → y ^ 3 = 1 → ∃ g, g * y * g⁻¹ = y3 := by
  decide +kernel

private theorem exists_conj_y5 : ∀ y : Perm (Fin 5), y ≠ 1 → y ^ 5 = 1 → ∃ g, g * y * g⁻¹ = y5 := by
  decide +kernel

private theorem comm_or_bad_y3 : ∀ t : Perm (Fin 5), Perm.sign t = -1 → t ^ 4 = 1 →
    (y3 * t = t * y3 ∧ t ^ 2 = 1) ∨ Bad y3 t := by
  decide +kernel

private theorem comm_or_bad_y5 : ∀ t : Perm (Fin 5), Perm.sign t = -1 → t ^ 4 = 1 →
    (y5 * t = t * y5 ∧ t ^ 2 = 1) ∨ Bad y5 t := by
  decide +kernel

private theorem swap_unique : ∀ y : Perm (Fin 5), y ≠ 1 → (y ^ 3 = 1 ∨ y ^ 5 = 1) →
    ∀ t : Perm (Fin 5), Perm.sign t = -1 → t ^ 2 = 1 → y * t = t * y →
    ∀ t' : Perm (Fin 5), Perm.sign t' = -1 → t' ^ 2 = 1 → y * t' = t' * y → t' = t := by
  decide +kernel

private theorem no_klein_four_centralizes_swap : ∀ t : Perm (Fin 5), Perm.sign t = -1 → t ^ 2 = 1 →
    ∀ k₁ : Perm (Fin 5), Perm.sign k₁ = 1 → k₁ ^ 2 = 1 → k₁ ≠ 1 → k₁ * t = t * k₁ →
    ∀ k₂ : Perm (Fin 5), Perm.sign k₂ = 1 → k₂ ^ 2 = 1 → k₂ ≠ 1 → k₂ ≠ k₁ →
      (k₁ * k₂) ^ 2 = 1 → k₂ * t = t * k₂ → False := by
  decide +kernel

private theorem alt_pow_four : ∀ k : Perm (Fin 5), Perm.sign k = 1 → k ^ 4 = 1 → k ^ 2 = 1 := by
  decide +kernel

private theorem pow_four_of_pow_eight : ∀ x : Perm (Fin 5), x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

private theorem bad_conj (g y t : Perm (Fin 5)) : Bad (g * y * g⁻¹) (g * t * g⁻¹) ↔ Bad y t := by
  have h : ∀ w : Perm (Fin 5), (g * w * g⁻¹) ^ 4 = 1 ↔ w ^ 4 = 1 := by
    intro w
    rw [conj_pow, mul_inv_eq_one, mul_eq_left]
  have hy2 : (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := conj_pow
  have e1 : g * t * g⁻¹ * (g * y * g⁻¹ * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹) =
      g * (t * (y * t * y⁻¹)) * g⁻¹ := by group
  have e2 : g * t * g⁻¹ * (g * y * g⁻¹ * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹)⁻¹ =
      g * (t * (y * t * y⁻¹)⁻¹) * g⁻¹ := by group
  have e3 : g * t * g⁻¹ * ((g * y * g⁻¹) ^ 2 * (g * t * g⁻¹) * ((g * y * g⁻¹) ^ 2)⁻¹) =
      g * (t * (y ^ 2 * t * (y ^ 2)⁻¹)) * g⁻¹ := by rw [hy2]; group
  have e4 : g * t * g⁻¹ * ((g * y * g⁻¹) ^ 2 * (g * t * g⁻¹) * ((g * y * g⁻¹) ^ 2)⁻¹)⁻¹ =
      g * (t * (y ^ 2 * t * (y ^ 2)⁻¹)⁻¹) * g⁻¹ := by rw [hy2]; group
  simp only [Bad, ne_eq, e1, e2, e3, e4, h]

private theorem comm_or_bad {y t : Perm (Fin 5)} (hy1 : y ≠ 1) (hy : y ^ 3 = 1 ∨ y ^ 5 = 1)
    (ht : Perm.sign t = -1) (ht4 : t ^ 4 = 1) : (y * t = t * y ∧ t ^ 2 = 1) ∨ Bad y t := by
  have key : ∀ y₀ g : Perm (Fin 5), g * y * g⁻¹ = y₀ →
      (∀ t : Perm (Fin 5), Perm.sign t = -1 → t ^ 4 = 1 →
        (y₀ * t = t * y₀ ∧ t ^ 2 = 1) ∨ Bad y₀ t) →
      (y * t = t * y ∧ t ^ 2 = 1) ∨ Bad y t := by
    intro y₀ g hg H
    have hs : Perm.sign (g * t * g⁻¹) = -1 := by
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, ht, mul_comm, ← mul_assoc]
      simp
    have h4 : (g * t * g⁻¹) ^ 4 = 1 := by rw [conj_pow, ht4]; group
    rcases H _ hs h4 with ⟨hc, h2⟩ | hb
    · refine Or.inl ⟨?_, ?_⟩
      · rw [← hg] at hc
        have : g * (y * t) * g⁻¹ = g * (t * y) * g⁻¹ :=
          calc g * (y * t) * g⁻¹ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
            _ = g * t * g⁻¹ * (g * y * g⁻¹) := hc
            _ = g * (t * y) * g⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel this)
      · have : g * t ^ 2 * g⁻¹ = 1 := by rw [← conj_pow]; exact h2
        simpa using this
    · rw [← hg] at hb
      exact Or.inr ((bad_conj g y t).mp hb)
  rcases hy with h3 | h5
  · obtain ⟨g, hg⟩ := exists_conj_y3 y hy1 h3
    exact key y3 g hg comm_or_bad_y3
  · obtain ⟨g, hg⟩ := exists_conj_y5 y hy1 h5
    exact key y5 g hg comm_or_bad_y5

private theorem pow_four_of_isPGroup {J : Subgroup (Perm (Fin 5))} (hJ : IsPGroup 2 J) :
    ∀ x ∈ J, x ^ 4 = 1 := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hJ) ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h120 : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
  have hdvd : 2 ^ k ∣ 120 := by
    have := orderOf_dvd_natCard x
    rwa [hk', h120] at this
  have hk3 : k ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ k := by omega
    have := (Nat.pow_dvd_pow 2 h4).trans hdvd
    norm_num at this
  have h8 : x ^ 8 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    exact Nat.pow_dvd_pow 2 hk3
  exact pow_four_of_pow_eight x h8

private theorem false_of_normalizes_odd {K J : Subgroup (Perm (Fin 5))} {y t : Perm (Fin 5)}
    (hK : K ≤ alternatingGroup (Fin 5)) (hKcard : Nat.card K = 4)
    (hKJ : K ≤ Subgroup.normalizer (J : Set (Perm (Fin 5)))) (hJ : IsPGroup 2 J)
    (hy1 : y ≠ 1) (hy : y ^ 3 = 1 ∨ y ^ 5 = 1)
    (hyJ : ∀ i : ℕ, y ^ i ∈ Subgroup.normalizer (J : Set (Perm (Fin 5))))
    (htJ : t ∈ J) (ht : Perm.sign t = -1) : False := by
  have hJ4 := pow_four_of_isPGroup hJ
  have hcomm : ∀ s ∈ J, Perm.sign s = -1 → y * s = s * y ∧ s ^ 2 = 1 := by
    intro s hsJ hs
    rcases comm_or_bad hy1 hy hs (hJ4 s hsJ) with h | hb
    · exact h
    · exfalso
      have hconj : ∀ i : ℕ, y ^ i * s * (y ^ i)⁻¹ ∈ J := fun i =>
        (Subgroup.mem_normalizer_iff.mp (hyJ i) s).mp hsJ
      have h1 : y * s * y⁻¹ ∈ J := by simpa using hconj 1
      have h2 : y ^ 2 * s * (y ^ 2)⁻¹ ∈ J := hconj 2
      rcases hb with hb | hb | hb | hb
      · exact hb (hJ4 _ (J.mul_mem hsJ h1))
      · exact hb (hJ4 _ (J.mul_mem hsJ (J.inv_mem h1)))
      · exact hb (hJ4 _ (J.mul_mem hsJ h2))
      · exact hb (hJ4 _ (J.mul_mem hsJ (J.inv_mem h2)))
  obtain ⟨hyt, ht2⟩ := hcomm t htJ ht
  have hKt : ∀ k ∈ K, k * t = t * k := by
    intro k hk
    have hkt : k * t * k⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hKJ hk) t).mp htJ
    have hs : Perm.sign (k * t * k⁻¹) = -1 := by
      rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, ht, mul_comm, ← mul_assoc]
      simp
    obtain ⟨hyt', ht2'⟩ := hcomm _ hkt hs
    have heq := swap_unique y hy1 hy t ht ht2 hyt (k * t * k⁻¹) hs ht2' hyt'
    calc k * t = k * t * k⁻¹ * k := by group
      _ = t * k := by rw [heq]
  have hK2 : ∀ k ∈ K, Perm.sign k = 1 ∧ k ^ 2 = 1 := by
    intro k hk
    have hsign : Perm.sign k = 1 := (Perm.mem_alternatingGroup.mp (hK hk))
    have h4 : (⟨k, hk⟩ : K) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
      rwa [hKcard] at this
    have h4' : k ^ 4 = 1 := by
      have := congrArg Subtype.val h4
      simpa using this
    exact ⟨hsign, alt_pow_four k hsign h4'⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : 2 < Fintype.card K := by
    rw [Fintype.card_eq_nat_card, hKcard]; norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
  have hu1 : (a⁻¹ * b : K) ≠ 1 := fun h => hab (inv_mul_eq_one.mp h)
  have hv1 : (a⁻¹ * c : K) ≠ 1 := fun h => hac (inv_mul_eq_one.mp h)
  have huv : (a⁻¹ * c : K) ≠ (a⁻¹ * b : K) := fun h => hbc (mul_left_cancel h).symm
  have hu : ((a⁻¹ * b : K) : Perm (Fin 5)) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hv : ((a⁻¹ * c : K) : Perm (Fin 5)) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have huv' : ((a⁻¹ * c : K) : Perm (Fin 5)) ≠ ((a⁻¹ * b : K) : Perm (Fin 5)) :=
    fun h => huv (Subtype.ext h)
  have hprod := hK2 _ (K.mul_mem (a⁻¹ * b : K).2 (a⁻¹ * c : K).2)
  exact no_klein_four_centralizes_swap t ht ht2
    _ (hK2 _ (a⁻¹ * b : K).2).1 (hK2 _ (a⁻¹ * b : K).2).2 hu (hKt _ (a⁻¹ * b : K).2)
    _ (hK2 _ (a⁻¹ * c : K).2).1 (hK2 _ (a⁻¹ * c : K).2).2 hv huv' hprod.2 (hKt _ (a⁻¹ * c : K).2)

theorem eq_bot_of_normalizes_odd_core {K J Y : Subgroup (Perm (Fin 5))} {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hK : K ≤ alternatingGroup (Fin 5)) (hKcard : Nat.card K = 4)
    (hKJ : K ≤ Subgroup.normalizer (J : Set (Perm (Fin 5)))) (hJ : IsPGroup 2 J)
    (hJodd : ∃ x ∈ J, Perm.sign x = -1)
    (hYJ : Y ≤ Subgroup.normalizer (J : Set (Perm (Fin 5)))) (hY : IsPGroup p Y) : Y = ⊥ := by
  by_contra hne
  have hpp : Nat.Prime p := by rcases hp with rfl | rfl; exacts [Nat.prime_three, Nat.prime_five]
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall Y).2 h)
  have hdvd : p ∣ orderOf (⟨y₀, hy₀Y⟩ : Y) :=
    hY.dvd_orderOf (fun h => hy₀ (congrArg Subtype.val h))
  obtain ⟨⟨y, hyY⟩, hyord⟩ :=
    exists_prime_orderOf_dvd_card' (G := Y) p (hdvd.trans (orderOf_dvd_natCard _))
  have hyord' : orderOf y = p := by rwa [Subgroup.orderOf_mk] at hyord
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord'
    exact hpp.one_lt.ne hyord'
  have hypow : y ^ p = 1 := by rw [← hyord']; exact pow_orderOf_eq_one y
  have hy : y ^ 3 = 1 ∨ y ^ 5 = 1 := by
    rcases hp with rfl | rfl
    · exact Or.inl hypow
    · exact Or.inr hypow
  obtain ⟨t, htJ, ht⟩ := hJodd
  exact false_of_normalizes_odd hK hKcard hKJ hJ hy1 hy (fun i => hYJ (Y.pow_mem hyY i)) htJ ht

theorem eq_bot_of_normalizes_odd {K S J Y : Subgroup (Perm (Fin 5))} {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hK : K ≤ alternatingGroup (Fin 5)) (hKcard : Nat.card K = 4) (hKS : K ≤ S)
    (hS : IsPGroup 2 S) (hJS : J ≤ S) (hJodd : ∃ x ∈ J, Perm.sign x = -1)
    (hSJ : S ≤ Subgroup.normalizer (J : Set (Perm (Fin 5))))
    (hYJ : Y ≤ Subgroup.normalizer (J : Set (Perm (Fin 5)))) (hY : IsPGroup p Y) : Y = ⊥ :=
  eq_bot_of_normalizes_odd_core hp hK hKcard (hKS.trans hSJ) (hS.to_le hJS) hJodd hYJ hY

end CFSG.Quasithin.A5S5
