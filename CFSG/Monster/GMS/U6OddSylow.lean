module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Monster.GMS.U6Odd

open Subgroup

section Sylow

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

omit [Finite H] in
theorem exists_sylow_eq (hp2 : ¬ p ^ 2 ∣ Nat.card H) (P : Subgroup H) (hP : Nat.card P = p) :
    ∃ S : Sylow p H, (S : Subgroup H) = P := by
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hidx : ¬ p ∣ P.index := by
    intro h
    apply hp2
    have := Subgroup.card_mul_index P
    rw [hP] at this
    rw [← this, pow_two]
    exact mul_dvd_mul_left p h
  exact ⟨hPp.toSylow hidx, rfl⟩

theorem card_normalizer_mul_card_sylow (S : Sylow p H) :
    Nat.card (normalizer ((S : Subgroup H) : Set H)) * Nat.card (Sylow p H) = Nat.card H := by
  rw [S.card_eq_index_normalizer]
  exact Subgroup.card_mul_index _

theorem card_normalizer_eq (hp2 : ¬ p ^ 2 ∣ Nat.card H) (P Q : Subgroup H) (hP : Nat.card P = p)
    (hQ : Nat.card Q = p) :
    Nat.card (normalizer (P : Set H)) = Nat.card (normalizer (Q : Set H)) := by
  obtain ⟨SP, rfl⟩ := exists_sylow_eq hp2 P hP
  obtain ⟨SQ, rfl⟩ := exists_sylow_eq hp2 Q hQ
  have h1 := card_normalizer_mul_card_sylow SP
  have h2 := card_normalizer_mul_card_sylow SQ
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

omit [Finite H] in
theorem exists_sylow_three (hH : Nat.card H = 2 ^ 15 * 3 ^ 6 * 5 * 7 * 11) (S : Subgroup H)
    (hS : Nat.card S = 3 ^ 6) : ∃ T : Sylow 3 H, (T : Subgroup H) = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 S := IsPGroup.of_card hS
  have hidx : ¬ 3 ∣ S.index := by
    have h := Subgroup.card_mul_index S
    rw [hS, hH] at h
    have h2 : S.index = 2 ^ 15 * 5 * 7 * 11 := by
      have : 3 ^ 6 * S.index = 3 ^ 6 * (2 ^ 15 * 5 * 7 * 11) := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    rw [h2]
    norm_num
  exact ⟨hPp.toSylow hidx, rfl⟩

end Sylow

section Inside

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_normalizer_subgroupOf (U₀ : Subgroup G) {g : G} (hg : g ∈ U₀) :
    Nat.card (normalizer (((zpowers g).subgroupOf U₀ : Subgroup U₀) : Set U₀)) =
      Nat.card ↥(normalizer ((zpowers g : Subgroup G) : Set G) ⊓ U₀) := by
  have hle : zpowers g ≤ U₀ := zpowers_le.2 hg
  rw [← subgroupOf_normalizer_eq hle, ← inf_subgroupOf_right]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv

omit [Finite G] in
theorem card_zpowers_subgroupOf (U₀ : Subgroup G) {g : G} (hg : g ∈ U₀) :
    Nat.card ((zpowers g).subgroupOf U₀) = orderOf g := by
  rw [← Nat.card_zpowers]
  exact Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hg)).toEquiv

theorem norm_data (U₀ : Subgroup G) {p : ℕ} [Fact p.Prime] (hp2 : ¬ p ^ 2 ∣ Nat.card U₀) {g : G}
    (hg : g ∈ U₀) (hord : orderOf g = p) :
    p ∣ Nat.card ↥(normalizer ((zpowers g : Subgroup G) : Set G) ⊓ U₀) ∧
      ∃ s : ℕ, Nat.card ↥(normalizer ((zpowers g : Subgroup G) : Set G) ⊓ U₀) * s =
        Nat.card U₀ ∧ s % p = 1 := by
  have hP₀ : Nat.card ((zpowers g).subgroupOf U₀) = p := by
    rw [card_zpowers_subgroupOf U₀ hg, hord]
  obtain ⟨S, hS⟩ := exists_sylow_eq hp2 _ hP₀
  rw [← card_normalizer_subgroupOf U₀ hg]
  refine ⟨?_, Nat.card (Sylow p U₀), ?_, ?_⟩
  · have := Subgroup.card_dvd_of_le (le_normalizer (H := (zpowers g).subgroupOf U₀))
    rwa [hP₀] at this
  · rw [← hS]
    exact card_normalizer_mul_card_sylow S
  · have h := card_sylow_modEq_one p U₀
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at h

theorem norm_field (U₀ : Subgroup G) {p D : ℕ} [Fact p.Prime] (hp2 : ¬ p ^ 2 ∣ Nat.card U₀)
    {g : G} (hg : g ∈ U₀) (hord : orderOf g = p)
    (hD : Nat.card ↥(normalizer ((zpowers g : Subgroup G) : Set G) ⊓ U₀) ∣ D) :
    ∀ P : Subgroup U₀, Nat.card P = p → ∀ N : Subgroup U₀, N ≤ normalizer (P : Set U₀) →
      Nat.card N ∣ D := by
  intro P hP N hN
  have hP₀ : Nat.card ((zpowers g).subgroupOf U₀) = p := by
    rw [card_zpowers_subgroupOf U₀ hg, hord]
  have h1 := card_normalizer_eq hp2 P _ hP hP₀
  rw [card_normalizer_subgroupOf U₀ hg] at h1
  exact (Subgroup.card_dvd_of_le hN).trans (h1 ▸ hD)

end Inside

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem card_le_mul_normalizer (P N : Subgroup G) {p : ℕ} (hp : p.Prime) (hP : Nat.card P = p)
    (hN : N ≤ normalizer (P : Set G)) :
    Nat.card N ≤ Nat.card ↥(N ⊓ centralizer (P : Set G)) * (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  let φ : N →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hker : φ.ker ≤ (N ⊓ centralizer (P : Set G)).subgroupOf N := by
    intro n hn
    have hn' : P.normalizerMonoidHom (Subgroup.inclusion hN n) = 1 := hn
    have hmem : Subgroup.inclusion hN n ∈ P.normalizerMonoidHom.ker := hn'
    rw [normalizerMonoidHom_ker] at hmem
    exact Subgroup.mem_inf.2 ⟨n.2, hmem⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ∣ p - 1 := by
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [IsCyclic.card_mulAut, hP, Nat.totient_prime hp] at this
  have h3 : Nat.card φ.ker ≤ Nat.card ↥(N ⊓ centralizer (P : Set G)) := by
    refine (Subgroup.card_le_of_le hker).trans ?_
    exact (Nat.card_congr
      (subgroupOfEquivOfLe (inf_le_left : N ⊓ centralizer (P : Set G) ≤ N)).toEquiv).le
  have h4 : Nat.card φ.range ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) h2
  calc Nat.card N = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(N ⊓ centralizer (P : Set G)) * (p - 1) := Nat.mul_le_mul h3 h4

end Normalizer

section Abelian

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem abelian_lt_of_sylow (S : Sylow p H) {B : ℕ}
    (hS : ∀ A : Subgroup H, A ≤ S → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A < B) :
    ∀ A : Subgroup H, IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A < B := by
  intro A hA hab
  obtain ⟨Q, hAQ⟩ := hA.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H S Q
  have hQ : ∀ x ∈ Q, c⁻¹ * x * c ∈ (S : Subgroup H) := by
    intro x hx
    have hx' : x ∈ ((c • S : Sylow p H) : Subgroup H) := by rw [hc]; exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨s, hs, rfl⟩ := hx'
    simpa [MulAut.smul_def, mul_assoc] using hs
  let A' : Subgroup H := A.map (MulAut.conj c⁻¹).toMonoidHom
  have hA'S : A' ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    have := hQ a (hAQ ha)
    simpa [MulAut.conj_apply, mul_assoc] using this
  have hab' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hab a ha b hb]
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  rw [← hcard]
  exact hS A' hA'S hab'

theorem abelian_map_subtype {G : Type*} [Group G] (U : Subgroup G) (A : Subgroup U)
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ x ∈ A.map U.subtype, ∀ y ∈ A.map U.subtype, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg (fun y : U => (y : G)) (hab a ha b hb)

end Abelian

theorem odd_dvd_of_dvd_mul_two_pow {n m : ℕ} (k : ℕ) (hodd : Odd n) (h : n ∣ m * 2 ^ k) :
    n ∣ m := by
  have hcop : Nat.Coprime n (2 ^ k) := by
    refine Nat.Coprime.pow_right k ?_
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by
      have := Nat.odd_iff.1 hodd
      omega))
  exact hcop.dvd_of_dvd_mul_right h

end CFSG.Monster.GMS.U6Odd
