module

public import CFSG.Quasithin.H13.A7FiveFixed

public section

namespace CFSG.Quasithin.H13.Lem19S

open Equiv Equiv.Perm CFSG.Quasithin.H13.A7

@[expose] def borelSet : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => σ 4 = 4 ∧ sign σ = 1

theorem pow_four_of_pow_eight : ∀ x : Perm (Fin 5), x ^ 8 = 1 → x ^ 4 = 1 := by
  decide +kernel

theorem exists_conj_not_two : ∀ s : Perm (Fin 5), s ∉ kleinV0Set → s ^ 4 = 1 →
    ∃ g ∈ borelSet, (s * (g * s * g⁻¹)) ^ 4 ≠ 1 := by
  decide +kernel

theorem borel_eq : ∀ c : Perm (Fin 5), NormalizesKleinV0 c → c ^ 3 = 1 → c ≠ 1 →
    ∀ b ∈ borelSet, ∃ v ∈ kleinV0Set, ∃ i : Fin 3, b = v * c ^ (i : ℕ) := by
  decide +kernel

theorem conj_ne_kleinV0 : ∀ c : Perm (Fin 5), NormalizesKleinV0 c → c ^ 3 = 1 → c ≠ 1 →
    ∀ v ∈ kleinV0Set, v ≠ 1 → c * v * c⁻¹ ≠ v := by
  decide +kernel

theorem not_quadratic : ∀ a b : Perm (Fin 5), (sign a = 1 ∧ sign b = 1 ∧ a * a = 1 ∧
    b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∃ m : Fin 5 → ZMod 2, (∑ x, m x) = 0 ∧ ∃ k : Fin 5,
      m (a⁻¹ (b⁻¹ k)) + m (b⁻¹ k) + m (a⁻¹ k) + m k ≠ 0 := by
  decide +kernel

theorem exists_moved : ∃ γ : Perm (Fin 5), sign γ = 1 ∧ ∃ m : Fin 5 → ZMod 2, (∑ x, m x) = 0 ∧
    ∃ k : Fin 5, m (γ⁻¹ k) ≠ m k := by
  decide +kernel

theorem kleinV0Set_mul_self : ∀ a ∈ kleinV0Set, a * a = 1 := by
  decide +kernel

theorem kleinV0Set_comm : ∀ a ∈ kleinV0Set, ∀ b ∈ kleinV0Set, a * b = b * a := by
  decide +kernel

theorem mul_self_of_card_four {S : Subgroup (Perm (Fin 5))} (hSA : S ≤ alternatingGroup (Fin 5))
    (hS4 : Nat.card S = 4) {s : Perm (Fin 5)} (hs : s ∈ S) : s * s = 1 := by
  obtain ⟨g, -, hg⟩ := exists_conj_kleinV0 hSA hS4
  have h := kleinV0Set_mul_self _ ((hg s).1 hs)
  calc s * s = g⁻¹ * (g * s * g⁻¹ * (g * s * g⁻¹)) * g := by group
    _ = 1 := by rw [h]; group

theorem comm_of_card_four {S : Subgroup (Perm (Fin 5))} (hSA : S ≤ alternatingGroup (Fin 5))
    (hS4 : Nat.card S = 4) {s t : Perm (Fin 5)} (hs : s ∈ S) (ht : t ∈ S) : s * t = t * s := by
  obtain ⟨g, -, hg⟩ := exists_conj_kleinV0 hSA hS4
  have h := kleinV0Set_comm _ ((hg s).1 hs) _ ((hg t).1 ht)
  calc s * t = g⁻¹ * (g * s * g⁻¹ * (g * t * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹ * (g * s * g⁻¹)) * g := by rw [h]
    _ = t * s := by group


theorem pow_four_of_isPGroup {R : Subgroup (Perm (Fin 5))} (hR : IsPGroup 2 R) {x : Perm (Fin 5)}
    (hx : x ∈ R) : x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 : orderOf x ∣ 120 := by
    have := orderOf_dvd_natCard x
    rwa [Nat.card_perm, Nat.card_fin] at this
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
    norm_num at h16
  have h8 : x ^ 8 = 1 := by
    have : orderOf x ∣ 8 := by
      rw [hj]
      exact (Nat.pow_dvd_pow 2 hj3).trans (by norm_num)
    exact orderOf_dvd_iff_pow_eq_one.mp this
  exact pow_four_of_pow_eight x h8

theorem le_of_normalizes {S R : Subgroup (Perm (Fin 5))} (hSA : S ≤ alternatingGroup (Fin 5))
    (hS4 : Nat.card S = 4) {c : Perm (Fin 5)} (hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hR : IsPGroup 2 R) (hRS : ∀ s ∈ S, ∀ x ∈ R, s * x * s⁻¹ ∈ R)
    (hRc : ∀ x ∈ R, c * x * c⁻¹ ∈ R) : R ≤ S := by
  obtain ⟨g, -, hg⟩ := exists_conj_kleinV0 hSA hS4
  set c' := g * c * g⁻¹ with hc'
  have hc'N : NormalizesKleinV0 c' := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ S := (hg _).2 (by
      rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
      exact ha)
    have h2 := (hg _).1 (hcS _ h1)
    rw [show g * (c * (g⁻¹ * a * g) * c⁻¹) * g⁻¹ = c' * a * c'⁻¹ by rw [hc']; group] at h2
    exact h2
  have hc'3 : c' ^ 3 = 1 := by rw [hc', conj_pow, hc3]; group
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    rw [hc'] at h
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hRci : ∀ i : ℕ, ∀ x ∈ R, c ^ i * x * (c ^ i)⁻¹ ∈ R := by
    intro i
    induction i with
    | zero => intro x hx; simpa using hx
    | succ i ih =>
      intro x hx
      have := hRc _ (ih x hx)
      rw [show c * (c ^ i * x * (c ^ i)⁻¹) * c⁻¹ = c ^ (i + 1) * x * (c ^ (i + 1))⁻¹ by
        rw [pow_succ']; group] at this
      exact this
  intro x hx
  set x' := g * x * g⁻¹ with hx'
  have hx'4 : x' ^ 4 = 1 := by
    rw [hx', conj_pow, pow_four_of_isPGroup hR hx]
    group
  by_contra hxS
  have hx'V : x' ∉ kleinV0Set := fun h => hxS ((hg x).2 h)
  obtain ⟨b, hb, hb4⟩ := exists_conj_not_two x' hx'V hx'4
  obtain ⟨v, hv, i, rfl⟩ := borel_eq c' hc'N hc'3 hc'1 b hb
  set s := g⁻¹ * v * g with hs
  have hsS : s ∈ S := (hg _).2 (by rw [hs, show g * (g⁻¹ * v * g) * g⁻¹ = v by group]; exact hv)
  set y := x * ((s * c ^ (i : ℕ)) * x * (s * c ^ (i : ℕ))⁻¹) with hy
  have hyR : y ∈ R := by
    refine R.mul_mem hx ?_
    have := hRS s hsS _ (hRci i x hx)
    rw [show s * (c ^ (i : ℕ) * x * (c ^ (i : ℕ))⁻¹) * s⁻¹ =
      s * c ^ (i : ℕ) * x * (s * c ^ (i : ℕ))⁻¹ by group] at this
    exact this
  apply hb4
  have e : x' * (v * c' ^ (i : ℕ) * x' * (v * c' ^ (i : ℕ))⁻¹) = g * y * g⁻¹ := by
    rw [hx', hc', hy, hs, conj_pow]
    group
  rw [e, conj_pow, pow_four_of_isPGroup hR hyR]
  group

theorem conj_ne {S : Subgroup (Perm (Fin 5))} (hSA : S ≤ alternatingGroup (Fin 5))
    (hS4 : Nat.card S = 4) {c : Perm (Fin 5)} (hcS : ∀ s ∈ S, c * s * c⁻¹ ∈ S) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) {v : Perm (Fin 5)} (hv : v ∈ S) (hv1 : v ≠ 1) : c * v * c⁻¹ ≠ v := by
  obtain ⟨g, -, hg⟩ := exists_conj_kleinV0 hSA hS4
  set c' := g * c * g⁻¹ with hc'
  have hc'N : NormalizesKleinV0 c' := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ S := (hg _).2 (by
      rw [show g * (g⁻¹ * a * g) * g⁻¹ = a by group]
      exact ha)
    have h2 := (hg _).1 (hcS _ h1)
    rw [show g * (c * (g⁻¹ * a * g) * c⁻¹) * g⁻¹ = c' * a * c'⁻¹ by rw [hc']; group] at h2
    exact h2
  have hc'3 : c' ^ 3 = 1 := by rw [hc', conj_pow, hc3]; group
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    rw [hc'] at h
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hv' : g * v * g⁻¹ ∈ kleinV0Set := (hg v).1 hv
  have hv'1 : g * v * g⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  intro h
  apply conj_ne_kleinV0 c' hc'N hc'3 hc'1 _ hv' hv'1
  rw [hc']
  calc g * c * g⁻¹ * (g * v * g⁻¹) * (g * c * g⁻¹)⁻¹ = g * (c * v * c⁻¹) * g⁻¹ := by group
    _ = g * v * g⁻¹ := by rw [h]

end CFSG.Quasithin.H13.Lem19S
