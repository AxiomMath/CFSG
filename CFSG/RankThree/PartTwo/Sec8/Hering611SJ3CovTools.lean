module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Sylow

theorem pow_four_inv_of_irred {X : Type*} [Group X] {R : Subgroup X}
    (hR : CFSG.Open.IsElemAbelian 3 R) (hR9 : Nat.card R = 9) {s : X}
    (hsN : s ∈ Subgroup.normalizer (R : Set X)) (hs8 : s ^ 8 = 1)
    (hirr : ∀ x ∈ R, x ≠ 1 → s * x * s⁻¹ ≠ 1 ∧ s * x * s⁻¹ ≠ x ∧ s * x * s⁻¹ ≠ x ^ 2)
    (hc4 : ∃ x ∈ R, s ^ 4 * x ≠ x * s ^ 4) :
    ∀ x ∈ R, s ^ 4 * x * (s ^ 4)⁻¹ = x⁻¹ := by
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [hR9]; norm_num)
  have hcomm : ∀ u ∈ R, ∀ v ∈ R, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h3 : ∀ u ∈ R, u ^ 3 = 1 := fun u hu => hR.2 u hu
  have hτ : s ^ 4 * s ^ 4 = 1 := by rw [← pow_add]; exact hs8
  have hτinv : (s ^ 4)⁻¹ = s ^ 4 := inv_eq_of_mul_eq_one_right hτ
  have hsR : ∀ x ∈ R, s * x * s⁻¹ ∈ R := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hsN x).1 hx
  have hτR : ∀ x ∈ R, s ^ 4 * x * (s ^ 4)⁻¹ ∈ R := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (pow_mem hsN 4) x).1 hx
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup X, F = R ⊓ Subgroup.centralizer ({s ^ 4} : Set X) :=
    ⟨_, rfl⟩
  have hmemF : ∀ x, x ∈ F ↔ x ∈ R ∧ x * s ^ 4 = s ^ 4 * x := by
    intro x
    rw [hFdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have FR : F ≤ R := fun x hx => ((hmemF x).1 hx).1
  have hdvd9 : Nat.card F ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le FR
    rwa [hR9, show (9 : ℕ) = 3 ^ 2 by norm_num] at this
  have hFne : F ≠ R := by
    obtain ⟨x0, hx0R, hx0⟩ := hc4
    intro h
    have hx0F : x0 ∈ F := by rw [h]; exact hx0R
    exact hx0 ((hmemF x0).1 hx0F).2.symm
  have hF9 : Nat.card F ≠ 9 := fun h => hFne (Subgroup.eq_of_le_of_card_ge FR (by omega))
  have hFs : ∀ x ∈ F, s * x * s⁻¹ ∈ F := by
    intro x hx
    obtain ⟨hxR, hxc⟩ := (hmemF x).1 hx
    rw [hmemF]
    refine ⟨hsR x hxR, ?_⟩
    calc s * x * s⁻¹ * s ^ 4 = s * (x * s ^ 4) * s⁻¹ := by group
      _ = s * (s ^ 4 * x) * s⁻¹ := by rw [hxc]
      _ = s ^ 4 * (s * x * s⁻¹) := by group
  have hbot : ∀ y ∈ F, y = 1 := by
    intro y hy
    by_contra hy1
    have hyR : y ∈ R := FR hy
    have hord : orderOf y = 3 := orderOf_eq_prime (h3 y hyR) hy1
    have hzle : Subgroup.zpowers y ≤ F := Subgroup.zpowers_le.2 hy
    have hz3 : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hord]
    have hzdvd : Nat.card (Subgroup.zpowers y) ∣ Nat.card F := Subgroup.card_dvd_of_le hzle
    rw [hz3] at hzdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd9
    have hF3 : Nat.card F = 3 := by
      interval_cases k
      · rw [pow_zero] at hk'; omega
      · rw [pow_one] at hk'; exact hk'
      · exact absurd (hk'.trans (by norm_num)) hF9
    have hFz : Subgroup.zpowers y = F := by
      haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
      exact Subgroup.eq_of_le_of_card_ge hzle (by omega)
    have hsy : s * y * s⁻¹ ∈ F := hFs y hy
    rw [← hFz, Subgroup.mem_zpowers_iff] at hsy
    obtain ⟨n, hn⟩ := hsy
    rw [← zpow_mod_orderOf, hord] at hn
    obtain ⟨h1, h2, h3'⟩ := hirr y hyR hy1
    have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3'' : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    generalize n % ((3 : ℕ) : ℤ) = r at hn h0 h3''
    interval_cases r
    · exact h1 (by simpa using hn.symm)
    · exact h2 (by simpa using hn.symm)
    · exact h3' (by simpa using hn.symm)
  intro z hz
  have hw : s ^ 4 * z * (s ^ 4)⁻¹ ∈ R := hτR z hz
  have hu : z * (s ^ 4 * z * (s ^ 4)⁻¹) ∈ F := by
    rw [hmemF]
    refine ⟨R.mul_mem hz hw, ?_⟩
    have hcz := hcomm _ hw z hz
    rw [hτinv] at hcz ⊢
    have e1 : s ^ 4 * (z * (s ^ 4 * z * s ^ 4)) = (s ^ 4 * z * s ^ 4 * z) * s ^ 4 := by
      group
    rw [e1, hcz]
  exact eq_inv_of_mul_eq_one_right (hbot _ hu)

theorem commutator_mem_zpowers_of_class_two {X : Type*} [Group X] {t₁ t₂ : X}
    (hc : ∀ x ∈ Subgroup.closure ({t₁, t₂} : Set X), ∀ y ∈ Subgroup.closure ({t₁, t₂} : Set X),
      ∀ g ∈ Subgroup.closure ({t₁, t₂} : Set X),
        (x * y * x⁻¹ * y⁻¹) * g = g * (x * y * x⁻¹ * y⁻¹)) :
    ∀ x ∈ Subgroup.closure ({t₁, t₂} : Set X), ∀ y ∈ Subgroup.closure ({t₁, t₂} : Set X),
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (t₁ * t₂ * t₁⁻¹ * t₂⁻¹) := by
  have key : ∀ c x : X, c * x = x * c → x⁻¹ * c⁻¹ * x = c⁻¹ := fun c x h =>
    ((show Commute x c from h.symm).inv_right).inv_mul_cancel
  have htP : ∀ t ∈ ({t₁, t₂} : Set X), t ∈ Subgroup.closure ({t₁, t₂} : Set X) :=
    fun t ht => Subgroup.subset_closure ht
  have hA : ∀ t ∈ ({t₁, t₂} : Set X), ∀ y ∈ Subgroup.closure ({t₁, t₂} : Set X),
      t * y * t⁻¹ * y⁻¹ ∈ Subgroup.zpowers (t₁ * t₂ * t₁⁻¹ * t₂⁻¹) := by
    intro t ht y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht hy
      rcases ht with h | h <;> rcases hy with h' | h' <;> rw [h, h']
      · rw [show t₁ * t₁ * t₁⁻¹ * t₁⁻¹ = 1 by group]; exact one_mem _
      · exact Subgroup.mem_zpowers _
      · rw [show t₂ * t₁ * t₂⁻¹ * t₁⁻¹ = (t₁ * t₂ * t₁⁻¹ * t₂⁻¹)⁻¹ by group]
        exact inv_mem (Subgroup.mem_zpowers _)
      · rw [show t₂ * t₂ * t₂⁻¹ * t₂⁻¹ = 1 by group]; exact one_mem _
    | one => rw [show t * 1 * t⁻¹ * 1⁻¹ = 1 by group]; exact one_mem _
    | mul a b ha hb iha ihb =>
      have hbc : (t * b * t⁻¹ * b⁻¹) * a = a * (t * b * t⁻¹ * b⁻¹) :=
        hc t (htP t ht) b hb a ha
      have hconj : a * (t * b * t⁻¹ * b⁻¹) * a⁻¹ = t * b * t⁻¹ * b⁻¹ := by
        rw [← hbc, mul_inv_cancel_right]
      have e : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
          (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
      rw [e, hconj]
      exact mul_mem iha ihb
    | inv a ha iha =>
      have hac : (t * a * t⁻¹ * a⁻¹) * a = a * (t * a * t⁻¹ * a⁻¹) :=
        hc t (htP t ht) a ha a ha
      have e : t * a⁻¹ * t⁻¹ * a⁻¹⁻¹ = a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ * a := by group
      rw [e, key _ _ hac]
      exact inv_mem iha
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hA x hx y hy
  | one => rw [show (1 : X) * y * 1⁻¹ * y⁻¹ = 1 by group]; exact one_mem _
  | mul a b ha hb iha ihb =>
    have hbc : (b * y * b⁻¹ * y⁻¹) * a = a * (b * y * b⁻¹ * y⁻¹) := hc b hb y hy a ha
    have hconj : a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ = b * y * b⁻¹ * y⁻¹ := by
      rw [← hbc, mul_inv_cancel_right]
    have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [e, hconj]
    exact mul_mem ihb iha
  | inv a ha iha =>
    have hac : (a * y * a⁻¹ * y⁻¹) * a = a * (a * y * a⁻¹ * y⁻¹) := hc a ha y hy a ha
    have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a := by group
    rw [e, key _ _ hac]
    exact inv_mem iha

end CFSG.AGLEmbedding.KFactProofs.J3Sylow
