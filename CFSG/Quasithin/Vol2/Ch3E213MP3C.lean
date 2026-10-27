module

public import CFSG.Quasithin.Vol2.Ch3E213MP3B

public section

namespace CFSG.Quasithin.Ch3E213M.P3

open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {K₁ : Subgroup Y}

theorem exists_not_isPGroup [IsSimpleGroup K₁] (hK2 : ¬ IsPGroup 2 K₁) {a : Y}
    (haN : a ∈ normalizer (K₁ : Set Y)) (haC : a ∉ centralizer (K₁ : Set Y)) :
    ∃ u ∈ K₁ ⊔ zpowers a, ¬ IsPGroup 2 (closure ({a, u⁻¹ * a * u} : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := K₁ ⊔ zpowers a with hX
  set a' : X := ⟨a, mem_sup_right (mem_zpowers a)⟩ with ha'
  by_contra h
  push Not at h
  have hP : a' ∈ CFSG.pCore 2 X := by
    refine (CFSG.GroupTheory.baer_conjugate_pair_p_core 2).2 a' fun g => ?_
    have e : (Subgroup.closure ({a', g⁻¹ * a' * g} : Set X)).map X.subtype =
        Subgroup.closure ({a, (g : Y)⁻¹ * a * g} : Set Y) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    have h1 := h g g.2
    rw [← e] at h1
    exact h1.of_equiv
      ((Subgroup.closure _).equivMapOfInjective X.subtype X.subtype_injective).symm
  apply haC
  set N := (CFSG.pCore 2 X ⊓ K₁.subgroupOf X).map X.subtype with hN
  have hNK : N ≤ K₁ := (map_mono inf_le_right).trans
    (map_subgroupOf_eq_of_le (le_sup_left : K₁ ≤ X)).le
  have hN2 : IsPGroup 2 N := (CFSG.pCore_isPGroup.map X.subtype).to_le (map_mono inf_le_left)
  have hKN : K₁ ≤ normalizer (N : Set Y) := by
    intro k hk
    refine mem_normalizer_fintype fun n hn => ?_
    obtain ⟨m, ⟨hmP, hmK⟩, rfl⟩ := hn
    set k' : X := ⟨k, mem_sup_left hk⟩
    refine ⟨k' * m * k'⁻¹, ⟨CFSG.pCore_normal.conj_mem m hmP k', ?_⟩, rfl⟩
    exact K₁.mul_mem (K₁.mul_mem hk hmK) (K₁.inv_mem hk)
  have hNb : N = ⊥ := by
    by_contra hne
    exact hK2 (H13.QRC.eq_of_normalized_of_simple hNK hKN hne ▸ hN2)
  rw [mem_centralizer_iff]
  intro k hk
  set k' : X := ⟨k, mem_sup_left hk⟩
  have hc : a * k * a⁻¹ * k⁻¹ ∈ N := by
    refine ⟨a' * k' * a'⁻¹ * k'⁻¹, ⟨?_, ?_⟩, rfl⟩
    · have h1 : k' * a'⁻¹ * k'⁻¹ ∈ CFSG.pCore 2 X :=
        CFSG.pCore_normal.conj_mem _ (inv_mem hP) k'
      have e : a' * k' * a'⁻¹ * k'⁻¹ = a' * (k' * a'⁻¹ * k'⁻¹) := by group
      rw [e]
      exact mul_mem hP h1
    · exact K₁.mul_mem ((mem_normalizer_iff.mp haN k).mp hk) (K₁.inv_mem hk)
  rw [hNb, mem_bot] at hc
  calc k * a = (a * k * a⁻¹ * k⁻¹)⁻¹ * (a * k) := by group
    _ = a * k := by rw [hc, inv_one, one_mul]

theorem exists_inverted [IsSimpleGroup K₁] (hK2 : ¬ IsPGroup 2 K₁) {a : Y} (ha : a * a = 1)
    (haN : a ∈ normalizer (K₁ : Set Y)) (haC : a ∉ centralizer (K₁ : Set Y)) :
    ∃ y ∈ K₁, ∃ ℓ b : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 1 ≤ b ∧ orderOf y = ℓ ^ b ∧ a * y * a = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, hnp⟩ := exists_not_isPGroup hK2 haN haC
  have hainv : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha).symm
  set w := u⁻¹ * a * u with hw
  set r := a * w with hr
  have hw2 : w * w = 1 := by
    calc w * w = u⁻¹ * (a * a) * u := by rw [hw]; group
      _ = 1 := by rw [ha]; group
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have hara : a * r * a = r⁻¹ := by
    rw [hr, mul_inv_rev, hwinv, hainv]
    calc a * (a * w) * a = (a * a) * w * a := by group
      _ = w * a := by rw [ha, one_mul]
  have hrK : r ∈ K₁ := by
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K₁ (zpowers a)
      (zpowers_le.mpr haN)] at hu
    obtain ⟨k, hk, z, hz, rfl⟩ := hu
    rcases eq_one_or_eq_of_mem_zpowers ha hz with hz1 | hza
    · have e : a * ((k * z)⁻¹ * a * (k * z)) = a * k⁻¹ * a⁻¹ * k := by
        rw [hz1, hainv]
        group
      rw [hr, hw, e]
      exact K₁.mul_mem ((mem_normalizer_iff.mp haN _).mp (K₁.inv_mem hk)) hk
    · have e : a * ((k * z)⁻¹ * a * (k * z)) = k⁻¹ * (a * k * a⁻¹) := by
        rw [hza, hainv]
        group
      rw [hr, hw, e]
      exact K₁.mul_mem (K₁.inv_mem hk) ((mem_normalizer_iff.mp haN k).mp hk)
  have haNr : a ∈ normalizer (zpowers r : Set Y) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show zpowers (MulAut.conj a r) = zpowers r
    rw [MulAut.conj_apply, hainv, hara, zpowers_inv]
  have hrnp : ¬ IsPGroup 2 (zpowers r) := by
    intro hrp
    apply hnp
    have hle : closure ({a, w} : Set Y) ≤ zpowers a ⊔ zpowers r := by
      rw [closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact mem_sup_left (mem_zpowers _)
      · rw [Set.mem_singleton_iff.mp hz]
        have e : w = a * r := by rw [hr, ← mul_assoc, ha, one_mul]
        rw [e]
        exact mul_mem (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers r))
    have hap : IsPGroup 2 (zpowers a) := fun x => ⟨1, Subtype.ext (by
      rcases eq_one_or_eq_of_mem_zpowers ha x.2 with h | h <;>
        simp [h, ha, pow_two])⟩
    exact (IsPGroup.to_sup_of_normal_right' hap hrp (zpowers_le.2 haNr)).to_le hle
  set n := orderOf r with hn
  have hn0 : n ≠ 0 := (orderOf_pos r).ne'
  obtain ⟨ℓ, hℓ, hℓ2, hℓn⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ n := by
    by_contra h
    push Not at h
    apply hrnp
    apply IsPGroup.of_card (n := n.primeFactorsList.length)
    rw [Nat.card_zpowers]
    exact Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun {d} hd hdn => by
      by_contra hd2
      exact h d hd hd2 hdn
  set b := n.factorization ℓ with hb
  have hb1 : 1 ≤ b := hℓ.factorization_pos_of_dvd hn0 hℓn
  have hdvd : ℓ ^ b ∣ n := Nat.ordProj_dvd n ℓ
  refine ⟨r ^ (n / ℓ ^ b), K₁.pow_mem hrK _, ℓ, b, hℓ, hℓ2, hb1,
    orderOf_pow_orderOf_div hn0 hdvd, ?_⟩
  have h1 : a * r ^ (n / ℓ ^ b) * a⁻¹ = (a * r * a⁻¹) ^ (n / ℓ ^ b) := (conj_pow).symm
  rw [hainv, hara, inv_pow] at h1
  exact h1

end CFSG.Quasithin.Ch3E213M.P3
