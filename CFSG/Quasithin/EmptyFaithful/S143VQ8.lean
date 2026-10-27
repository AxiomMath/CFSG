module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Quasithin.EmptyFaithful.S143UA

public section

namespace CFSG.Quasithin.S143V

theorem nonempty_mulEquiv_quaternion {A : Type*} [Group A] [Finite A] (hcard : Nat.card A = 8)
    {z : A} (hz1 : z ≠ 1) (hzc : ∀ a : A, a * z = z * a)
    (hsq : ∀ a : A, a ≠ 1 → a ≠ z → a ^ 2 = z) : Nonempty (A ≃* QuaternionGroup 2) := by
  obtain ⟨x, hx1, hxz⟩ : ∃ x : A, x ≠ 1 ∧ x ≠ z := by
    by_contra hcon
    have hsub : (Set.univ : Set A) ⊆ {1, z} := fun a _ => by
      by_cases h1 : a = 1
      · exact Or.inl h1
      · by_cases h2 : a = z
        · exact Or.inr h2
        · exact absurd ⟨a, h1, h2⟩ hcon
    have h2 : Nat.card A ≤ 2 := by
      calc Nat.card A = (Set.univ : Set A).ncard := (Set.ncard_univ A).symm
        _ ≤ ({1, z} : Set A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          have := Set.ncard_insert_le (1 : A) ({z} : Set A)
          rwa [Set.ncard_singleton] at this
    omega
  have hx2 : x ^ 2 = z := hsq x hx1 hxz
  have hx8 : x ^ 8 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hxz1 : x * z ≠ 1 := by
    intro h
    have h3 : x ^ 3 = 1 := by
      calc x ^ 3 = x * x ^ 2 := by group
        _ = x * z := by rw [hx2]
        _ = 1 := h
    have hdvd : orderOf x ∣ Nat.gcd 3 8 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hx8)
    exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hdvd)))
  have hxzz : x * z ≠ z := fun h => hx1 (by simpa using h)
  have hz2 : z ^ 2 = 1 := by
    have h := hsq (x * z) hxz1 hxzz
    rw [Commute.mul_pow (hzc x), hx2] at h
    exact mul_eq_left.mp h
  have hx4 : x ^ (2 * 2) = 1 := by rw [pow_mul, hx2, hz2]
  have hord : orderOf x = 4 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · simpa [hx2] using hz1
    · simpa using hx4
  have hzp : Nat.card (Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hord]
  obtain ⟨y, hy⟩ : ∃ y : A, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    have htop : Subgroup.zpowers x = ⊤ :=
      (Subgroup.eq_top_iff' _).mpr fun a => by_contra fun h => hcon ⟨a, h⟩
    rw [htop, Subgroup.card_top, hcard] at hzp
    omega
  have hzmem : z ∈ Subgroup.zpowers x := hx2 ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hyz : y ≠ z := fun h => hy (h ▸ hzmem)
  have hy2 : y ^ 2 = z := hsq y hy1 hyz
  have hyx1 : y * x ≠ 1 := fun h => hy (by
    rw [eq_inv_of_mul_eq_one_left h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hyxz : y * x ≠ z := fun h => hy (by
    rw [eq_mul_inv_of_mul_eq h]
    exact Subgroup.mul_mem _ hzmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)))
  have hyx2 : (y * x) ^ 2 = z := hsq (y * x) hyx1 hyxz
  have hxyx : x * y * x = y := by
    refine mul_left_cancel (a := y) ?_
    calc y * (x * y * x) = (y * x) ^ 2 := by rw [pow_two]; group
      _ = z := hyx2
      _ = y * y := by rw [← hy2, pow_two]
  have hconj : y * x * y⁻¹ = x⁻¹ := by
    calc y * x * y⁻¹ = x⁻¹ * (x * y * x) * y⁻¹ := by group
      _ = x⁻¹ := by rw [hxyx]; group
  have hyx : y ^ 2 = x ^ 2 := hy2.trans hx2.symm
  have hinj := CFSG.Quasithin.S143.SL23.normalFormHom_injective hord hy hx4 hyx hconj
  have hQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hbij := hinj.bijective_of_nat_card_le (by rw [hQ, hcard])
  exact ⟨(MulEquiv.ofBijective _ hbij).symm⟩

private theorem nonempty_mulEquiv_quaternion_comap {P E : Type*} [Group P] [Finite P] [CommGroup E]
    (π : P →* E) (hπ : Function.Surjective π) {z : P} (hz1 : z ≠ 1) (hzc : ∀ x : P, x * z = z * x)
    (hker : ∀ x : P, π x = 1 ↔ (x = 1 ∨ x = z)) (hexp : ∀ e : E, e * e = 1)
    (hP : Nat.card P = 32) (hE : Nat.card E = 16) (U : Subgroup E) (hU : Nat.card U = 4)
    (hanis : ∀ x : P, π x ∈ U → π x ≠ 1 → x ^ 2 ≠ 1) :
    Nonempty (↥(U.comap π) ≃* QuaternionGroup 2) := by
  have hzA : z ∈ U.comap π := by
    rw [Subgroup.mem_comap, (hker z).mpr (Or.inr rfl)]
    exact U.one_mem
  have hAcard : Nat.card (U.comap π) = 8 := by
    have h1 := Subgroup.card_mul_index (U.comap π)
    have h2 : (U.comap π).index = U.index := Subgroup.index_comap_of_surjective U hπ
    have h3 := Subgroup.card_mul_index U
    rw [h2, hP] at h1
    rw [hU, hE] at h3
    have h4 : U.index = 4 := by omega
    rw [h4] at h1
    omega
  refine nonempty_mulEquiv_quaternion (z := ⟨z, hzA⟩) hAcard ?_ ?_ ?_
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · intro a
    exact Subtype.ext (hzc a.1)
  · intro a ha1 haz
    have hπa : π a.1 ∈ U := a.2
    have hne : π a.1 ≠ 1 := fun h => by
      rcases (hker a.1).mp h with h1 | h1
      · exact ha1 (Subtype.ext h1)
      · exact haz (Subtype.ext h1)
    have hsq1 : a.1 ^ 2 ≠ 1 := hanis a.1 hπa hne
    have hsq2 : π (a.1 ^ 2) = 1 := by rw [map_pow, pow_two]; exact hexp _
    rcases (hker _).mp hsq2 with h | h
    · exact absurd h hsq1
    · exact Subtype.ext (by simpa using h)

theorem isQ8Sq_of_orthogonal_planes {P E : Type*} [Group P] [Finite P] [CommGroup E] (π : P →* E)
    (hπ : Function.Surjective π) {z : P} (hz1 : z ≠ 1) (hzc : ∀ x : P, x * z = z * x)
    (hker : ∀ x : P, π x = 1 ↔ (x = 1 ∨ x = z)) (hexp : ∀ e : E, e * e = 1)
    (U₁ U₂ : Subgroup E) (hinf : U₁ ⊓ U₂ = ⊥) (hsup : U₁ ⊔ U₂ = ⊤)
    (hU₁ : Nat.card U₁ = 4) (hU₂ : Nat.card U₂ = 4)
    (hanis₁ : ∀ x : P, π x ∈ U₁ → π x ≠ 1 → x ^ 2 ≠ 1)
    (hanis₂ : ∀ x : P, π x ∈ U₂ → π x ≠ 1 → x ^ 2 ≠ 1)
    (horth : ∀ a b : P, π a ∈ U₁ → π b ∈ U₂ → a * b = b * a) : IsQ8Sq P := by
  have : Finite E := Finite.of_surjective π hπ
  have hkerc : Nat.card π.ker = 2 := by
    have hset : (π.ker : Set P) = {1, z} := by
      ext x
      simp [hker]
    calc Nat.card π.ker = (π.ker : Set P).ncard := Nat.card_coe_set_eq _
      _ = 2 := by rw [hset]; exact Set.ncard_pair hz1.symm
  have hE : Nat.card E = 16 := by
    have h := (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top])).card_mul_card
    rw [hU₁, hU₂] at h
    omega
  have hP : Nat.card P = 32 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hπ
    rw [hkerc, hE] at h
    omega
  refine ⟨hP, U₁.comap π, U₂.comap π, ⟨?_, ?_⟩,
    nonempty_mulEquiv_quaternion_comap π hπ hz1 hzc hker hexp hP hE U₁ hU₁ hanis₁,
    nonempty_mulEquiv_quaternion_comap π hπ hz1 hzc hker hexp hP hE U₂ hU₂ hanis₂⟩
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (horth a b ha hb).symm
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y₁, hy₁, y₂, hy₂, hxy⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top (π x))
    obtain ⟨a, rfl⟩ := hπ y₁
    obtain ⟨b, rfl⟩ := hπ y₂
    have ha : a ∈ U₁.comap π := hy₁
    have hb : b ∈ U₂.comap π := hy₂
    have hk : π ((a * b)⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, map_mul, hxy, inv_mul_cancel]
    have hkA : (a * b)⁻¹ * x ∈ U₁.comap π := by
      rw [Subgroup.mem_comap, hk]
      exact U₁.one_mem
    have hxe : x = a * b * ((a * b)⁻¹ * x) := by group
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem_sup ha hb) (Subgroup.mem_sup_left hkA)

end CFSG.Quasithin.S143V
