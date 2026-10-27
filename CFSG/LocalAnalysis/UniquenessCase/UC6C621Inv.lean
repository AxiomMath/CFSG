module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C621b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools

@[expose] def InvNormalizer (p : ℕ) (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, Nat.card X = p ^ 2 * n ∧ ¬ p ∣ n ∧ ∃ E₀ : Subgroup X, Nat.card E₀ = p ^ 2 ∧
    (∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a) ∧ ∃ x₀ ∈ normalizer (E₀ : Set X),
      ∀ e ∈ E₀, x₀ * x₀ * e * (x₀ * x₀)⁻¹ = e⁻¹

theorem isSylowOf_top_of_card {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {P : Subgroup X}
    {k n : ℕ} (hP : Nat.card P = p ^ k) (hX : Nat.card X = p ^ k * n) (hn : ¬ p ∣ n) :
    IsSylowOf p P ⊤ := by
  rw [isSylowOf_iff]
  refine ⟨le_top, IsPGroup.of_card hP, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hidx : P.index = n := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [Subgroup.card_mul_index, hX, hP]
  rwa [hidx]

theorem InvNormalizer.of_mulEquiv {p : ℕ} {X Y : Type} [Group X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : InvNormalizer p X) : InvNormalizer p Y := by
  obtain ⟨n, hn, hpn, E₀, hE₀, hab, x₀, hx₀, hinv⟩ := h
  refine ⟨n, by rw [← Nat.card_congr e.toEquiv]; exact hn, hpn, E₀.map e.toMonoidHom, ?_, ?_, e x₀, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hE₀
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hab a ha b hb]
  · refine mem_normalizer_of_forward_uc6 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨x₀ * a * x₀⁻¹, (mem_normalizer_iff.1 hx₀ a).1 ha, by simp⟩
  · rintro _ ⟨a, ha, rfl⟩
    have := hinv a ha
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_inv, this]

theorem commute_of_mem_zpowers {G : Type*} [Group G] {u v : G} (h : u * v = v * u) :
    ∀ s ∈ zpowers u, ∀ t ∈ zpowers v, s * t = t * s := by
  intro s hs t ht
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  exact (Commute.zpow_zpow (show Commute u v from h) i j).eq

theorem orderOf_eq_three_of_pow_three {G : Type*} [Group G] {u : G} (hu : u ^ 3 = 1) (hu1 : u ≠ 1) :
    orderOf u = 3 := by
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hu) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hu1
  · exact h

theorem invNormalizer_of_data {X : Type} [Group X] [Finite X] {u v x : X} {n : ℕ}
    (hcard : Nat.card X = 9 * n) (hn : ¬ 3 ∣ n) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hvu : v ≠ u) (hvu2 : v ≠ u ^ 2)
    (hxu : x * u * x⁻¹ ∈ zpowers u ⊔ zpowers v) (hxv : x * v * x⁻¹ ∈ zpowers u ⊔ zpowers v)
    (hyu : x * x * u * (x * x)⁻¹ = u⁻¹) (hyv : x * x * v * (x * x)⁻¹ = v⁻¹) :
    InvNormalizer 3 X := by
  have hzu : Nat.card (zpowers u) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow_three hu hu1]
  have hzv : Nat.card (zpowers v) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow_three hv hv1]
  have hcomm := commute_of_mem_zpowers huv
  have hinv2 : u⁻¹ = u ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hu) : u ^ 2 = u⁻¹).symm
  have hdisj : zpowers u ⊓ zpowers v = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have h1 := eq_one_or_eq_or_eq_inv_of_card_three hzu (Subgroup.mem_zpowers u) hu1 hu hw.1
    have h2 := eq_one_or_eq_or_eq_inv_of_card_three hzv (Subgroup.mem_zpowers v) hv1 hv hw.2
    rcases h1 with h1 | h1 | h1
    · exact h1
    · rw [h1] at h2
      rcases h2 with h2 | h2 | h2
      · exact absurd h2 hu1
      · exact absurd h2.symm hvu
      · exact absurd (by rw [← hinv2, h2, inv_inv]) hvu2
    · rw [h1] at h2
      rcases h2 with h2 | h2 | h2
      · exact absurd (inv_eq_one.1 h2) hu1
      · exact absurd (by rw [← h2, hinv2]) hvu2
      · exact absurd (inv_injective h2).symm hvu
  have hcardE : Nat.card ↥(zpowers u ⊔ zpowers v) = 9 := by
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, hzu, hzv]
  have habE : ∀ a ∈ zpowers u ⊔ zpowers v, ∀ b ∈ zpowers u ⊔ zpowers v, a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm ha
    obtain ⟨s', hs', t', ht', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.1 hs'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    obtain ⟨j', rfl⟩ := Subgroup.mem_zpowers_iff.1 ht'
    have hss : u ^ i * u ^ i' = u ^ i' * u ^ i := ((Commute.refl u).zpow_zpow i i').eq
    have htt : v ^ j * v ^ j' = v ^ j' * v ^ j := ((Commute.refl v).zpow_zpow j j').eq
    calc u ^ i * v ^ j * (u ^ i' * v ^ j') = u ^ i * (v ^ j * u ^ i') * v ^ j' := by group
      _ = u ^ i * (u ^ i' * v ^ j) * v ^ j' := by rw [← hcomm _ hs' _ ht]
      _ = (u ^ i * u ^ i') * (v ^ j * v ^ j') := by group
      _ = (u ^ i' * u ^ i) * (v ^ j' * v ^ j) := by rw [hss, htt]
      _ = u ^ i' * (u ^ i * v ^ j') * v ^ j := by group
      _ = u ^ i' * (v ^ j' * u ^ i) * v ^ j := by rw [hcomm _ hs _ ht']
      _ = u ^ i' * v ^ j' * (u ^ i * v ^ j) := by group
  have hnorm : ∀ e ∈ zpowers u ⊔ zpowers v, x * e * x⁻¹ ∈ zpowers u ⊔ zpowers v := by
    intro e he
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    have h1 : x * (u ^ i * v ^ j) * x⁻¹ = (x * u * x⁻¹) ^ i * (x * v * x⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [h1]
    exact (zpowers u ⊔ zpowers v).mul_mem (zpow_mem hxu i) (zpow_mem hxv j)
  have hinv : ∀ e ∈ zpowers u ⊔ zpowers v, x * x * e * (x * x)⁻¹ = e⁻¹ := by
    intro e he
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    have h1 : x * x * (u ^ i * v ^ j) * (x * x)⁻¹ =
        (x * x * u * (x * x)⁻¹) ^ i * (x * x * v * (x * x)⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [h1, hyu, hyv, mul_inv_rev, ← inv_zpow, ← inv_zpow]
    exact ((Commute.inv_inv (show Commute u v from huv)).zpow_zpow i j).eq
  exact ⟨n, by rw [hcard]; norm_num, hn, zpowers u ⊔ zpowers v, by rw [hcardE]; norm_num, habE, x,
    mem_normalizer_of_forward_uc6 hnorm, hinv⟩

theorem invNormalizer_of_cycle {X : Type} [Group X] [Finite X] {u v x : X} {n : ℕ}
    (hcard : Nat.card X = 9 * n) (hn : ¬ 3 ∣ n) (hu : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hxu : x * u * x⁻¹ = v) (huv : u * v = v * u) (hvu : v ≠ u) (hvu2 : v ≠ u ^ 2)
    (hy : x * x * u * (x * x)⁻¹ = u⁻¹) : InvNormalizer 3 X := by
  have hv3 : v ^ 3 = 1 := by
    rw [← hxu, conj_pow, hu]
    group
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hu1
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [hxu]; group
  have hxv : x * v * x⁻¹ = u⁻¹ := by
    rw [← hy, ← hxu]
    group
  have hyv : x * x * v * (x * x)⁻¹ = v⁻¹ := by
    calc x * x * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
      _ = (x * u * x⁻¹)⁻¹ := by rw [hxv]; group
      _ = v⁻¹ := by rw [hxu]
  have hm1 : x * u * x⁻¹ ∈ zpowers u ⊔ zpowers v := by
    rw [hxu]
    exact mem_sup_right (Subgroup.mem_zpowers v)
  have hm2 : x * v * x⁻¹ ∈ zpowers u ⊔ zpowers v := by
    rw [hxv]
    exact mem_sup_left (inv_mem (Subgroup.mem_zpowers u))
  exact invNormalizer_of_data hcard hn hu hv3 huv hu1 hv1 hvu hvu2 hm1 hm2 hy hyv

end CFSG.LocalAnalysis.UniquenessCase.UC6
